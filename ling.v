Require Import Bool Arith List.
Require Import Coq.Program.Equality.
Load hlist.
Load syntax.
Set Implicit Arguments.
Set Asymmetric Patterns.

Example inc : exp nil (TList TNat) :=
  emap (eplus (evar HFirst) (econst 3)) (econs (econst 4) enil).

Example let_ex : exp nil TNat :=
  elet (econst 42) (eplus (evar HFirst) (econst 10)).

Example app_prog : exp nil (TList TNat) := eappend (econs (econst 0) enil) (econs (econst 1) enil).

Fixpoint insertAt (t : ty) (G : list ty) (n : nat) {struct n}
  : list ty :=
  match n with
  | O => t :: G
  | S n' => match G with
            | nil => t :: G
            | t' :: G' => t' :: insertAt t G' n'
            end
  end.

Fixpoint liftVar t G (x : member t G) t' n
  : member t (insertAt t' G n) :=
  match x with
  | HFirst G' => match n return member t (insertAt t' (t :: G') n) with
                 | O => HNext HFirst
                 | _ => HFirst
                 end
  | HNext t'' G' x' => match n return member t (insertAt t' (t'' :: G') n) with
                       | O => HNext (HNext x')
                       | S n' => HNext (liftVar x' t' n')
                       end
  end.

Example nested_map : exp nil (TList TNat) :=
  emap (eplus (econst 3) (evar HFirst))
  (emap (eplus (evar HFirst) (econst 10)) [| econst 1 ; econst 2 ; econst 3 |]).

Example flat_map : exp nil (TList TNat) :=
  emap (eplus (econst 3) (eplus (evar HFirst) (econst 10)))
       [| econst 1 ; econst 2 ; econst 3 |].


Fixpoint tyDenote (t : ty) : Type :=
  match t with
  | TBool => bool
  | TNat => nat
  | TList t => list (tyDenote t)
  end.

Fixpoint valDenote t (v : val t) : tyDenote t :=
  match v with
  | vfalse => false
  | vtrue => true
  | vconst n => n
  | vnil _ => nil
  | vcons _ v1 v2 => (valDenote v1) :: (valDenote v2)
  end.

(* An interpreter *)
Fixpoint expDenote G t (e : exp G t) : hlist tyDenote G -> tyDenote t :=
  match e with
  | evar _ _ x => fun s => hget s x
  | econst _ n => fun _ => n
  | etrue _ => fun _ => true
  | efalse _ => fun _ => false
  | eplus _ e1 e2 => fun s => (expDenote e1 s) + (expDenote e2 s)
  | enil _ _ => fun _ => nil
  | econs _ _ e1 e2 => fun s => (expDenote e1 s) :: (expDenote e2 s)
  | elet _ _ _ e el =>
    fun s => expDenote el (HCons (expDenote e s) s)
  | eappend _ _ e1 e2 => fun s => app (expDenote e1 s) (expDenote e2 s)
  | emap _ _ _ ef e =>
    fun s => let f := fun x => expDenote ef (HCons x s)
             in map f (expDenote e s)
  end.

Eval compute in (expDenote app_prog) HNil.
Eval compute in (expDenote let_ex) HNil.
Eval compute in (expDenote inc) HNil.

Lemma append_assoc : forall G t (e1 e2 e3: exp G (TList t)) s,
    expDenote (eappend (eappend e1 e2) e3) s =
    expDenote (eappend e1 (eappend e2 e3)) s.
Proof.
  intros.
  simpl.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Example dummy_proof : expDenote nested_map = expDenote flat_map.
simpl.
reflexivity.
Qed.

(* map f (map g) xs = map (f o g) xs
 * replace all occurences of x in f by result of g
 *)

Check emap.
Check @HNext.

Fixpoint subst_first G t t1 t2
         (ef' : exp (t1 :: G) t2)
         (ef : exp (t2 :: G) t)
  : exp (t1 :: G) t :=
  match ef with
  | evar _ _ (HFirst _) => ef'
  | evar _ _ x => evar x
  | econst _ n => econst _ n
  | etrue _ => etrue _
  | _ => ef
  end.

Definition fuse_map G t (e : exp G t) : exp G t :=
  match e with
  | emap G' t1' t2' ef' e' =>
    match e' with
    | emap G'' t1'' t2'' ef'' e'' => emap G' t1' t2' ef'' e'
    | _ => e'
    end
  | _ => e
  end.
      
(* Inductive judgment for append *)
Inductive CApp : forall t,
    val (TList t) -> val (TList t) -> val (TList t) -> Prop :=
| CAppNil : forall t (v : val (TList t)), CApp (vnil t) v v
| CAppCons : forall t v (v1 : val t) v2 v3,
    CApp v2 v3 v -> CApp (vcons v1 v2) v3 (vcons v1 v).

(* The beginning of an inductive judgment for map
 * This may need to be mutally inductive with Ev
 *)
Inductive CMap : forall G t1 t2,
    val (TList t1) -> exp G t2 -> val (TList t2) -> Prop :=
| CMapNil : forall G t1 t2 (e : exp G t2), CMap (vnil t1) e (vnil t2).

(* The start of an inductive evaluation relation *)
Inductive Ev : forall t, exp nil t -> val t -> Prop :=
| EvTrue : Ev etrue vtrue
| EvFalse : Ev efalse vfalse
| EvConst : forall n, Ev (econst n) (vconst n)
| EvNil : forall t, Ev enil (vnil t)
| EvCons : forall t (e1 : exp nil t) (e2 : exp nil (TList t))
                  (v1 : val t) (v2 : val (TList t)),
    Ev e1 v1 -> Ev e2 v2 -> Ev (econs e1 e2) (vcons v1 v2)
| EvAppend : forall t (e1 : exp nil (TList t)) (e2 : exp nil (TList t)) v1 v2 v,
    Ev e1 v1 -> Ev e2 v2 -> CApp v1 v2 v -> Ev (eappend e1 e2) v.

Example ev_example :
  Ev etrue vtrue.
apply EvTrue.
Qed.

(* CApp is deterministic *)
Lemma capp_determ : forall t (v1 v2 v3 v4 : val (TList t)),
    CApp v1 v2 v3 -> CApp v1 v2 v4 -> v3 = v4.
Proof.
  intros.
  dependent induction H.
  dependent destruction H0.
  reflexivity.
  dependent destruction H0.
  rewrite (IHCApp v0).
  reflexivity.
  assumption.
Qed.

(* Evaluation relation is deterministic *)
Lemma ev_determ : forall t (e: exp nil t) v1 v2,
    Ev e v1 -> Ev e v2 -> v1 = v2.
  Proof.
    intros.
    dependent induction H;
    try (dependent destruction H0;
         reflexivity).
    dependent destruction H1.
    rewrite (IHEv1 v3).
    rewrite (IHEv2 v4).
    reflexivity.
    assumption.
    assumption.
    dependent destruction H2.
    eapply capp_determ.
    eassumption.
    rewrite (IHEv1 v3).
    rewrite (IHEv2 v4).
    assumption.
    assumption.
    assumption.
Qed.

  