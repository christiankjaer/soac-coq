Require Import Bool Arith List.
Require Import Coq.Program.Equality.
Require Import Program.
Load hlist.
Load syntax.
Set Implicit Arguments.
Set Asymmetric Patterns.

Example inc : exp nil (TList TNat) :=
  emap (eplus (evar zvar) (econst 3)) (econs (econst 4) enil).

Example let_ex : exp nil TNat :=
  elet (econst 42) (eplus (evar zvar) (econst 10)).

Example app_prog : exp nil (TList TNat) := eappend (econs (econst 0) enil) (econs (econst 1) enil).

Example nested_map : exp nil (TList TNat) :=
  emap (eplus (econst 3) (evar zvar))
  (emap (eplus (evar zvar) (econst 10)) [| econst 1 ; econst 2 ; econst 3 |]).

Example flat_map : exp nil (TList TNat) :=
  emap (eplus (econst 3) (eplus (evar zvar) (econst 10)))
       [| econst 1 ; econst 2 ; econst 3 |].

Definition Sub G G' := forall t, var G t -> exp G' t. 

Definition idSub {G} : Sub G G := @evar G.

Program Definition consSub {G G' t} (e:exp G' t) (s:Sub G G') : Sub (t::G) G' :=
  fun t' (v: var (t::G) t') =>
    match v with
    | zvar _ _ => e
    | svar _ _ _ v' => s _ v'
    end.
    
Notation "{| e ; .. ; f |}" := (consSub e .. (consSub f idSub) ..).

Definition Ren G G' := forall t, var G t -> var G' t.

Program Definition renameLift {G G' t}
        (r : Ren G G') : Ren (t :: G) (t :: G') :=
  fun t' v =>
    match v with
    | zvar _ _ => zvar
    | svar _ _ _ v' => svar (r _ v')
    end.

Fixpoint renameExp G G' t (r : Ren G G') (e : exp G t) :=
  match e with
  | evar _ x => evar (r _ x)
  | etrue => etrue
  | efalse => efalse
  | econst n => econst n
  | eplus e1 e2 => eplus (renameExp r e1) (renameExp r e2)
  | enil _ => enil
  | econs _ e1 e2 => econs (renameExp r e1) (renameExp r e2)
  | elet _ _ e1 e2 => elet (renameExp r e1) (renameExp (renameLift r) e2)
  | eappend _ e1 e2 => eappend (renameExp r e1) (renameExp r e2)
  | emap _ _ e1 e2 => emap (renameExp (renameLift r) e1) (renameExp r e2)
  | efilter _ e1 e2 => efilter (renameExp (renameLift r) e1) (renameExp r e2)
  end.

Definition shiftExp G t t' : exp G t -> exp (t' :: G) t :=
  renameExp (fun _ v => svar v).

Program Definition
        subShift {G G'} t (s : Sub G G') : Sub (t :: G) (t :: G') :=
  fun t' v =>
    match v with
    | zvar _ _ => evar zvar
    | svar _ _ _ v' => shiftExp t (s _ v')
    end.

Fixpoint subExp G G' t (s : Sub G G') (e : exp G t) :=
  match e with
  | evar _ x => s _ x
  | etrue => etrue
  | efalse => efalse
  | econst n => econst n
  | eplus e1 e2 => eplus (subExp s e1) (subExp s e2)
  | enil _ => enil
  | econs _ e1 e2 => econs (subExp s e1) (subExp s e2)
  | elet _ _ e1 e2 => elet (subExp s e1) (subExp (subShift s) e2)
  | eappend _ e1 e2 => eappend (subExp s e1) (subExp s e2)
  | emap _ _ e1 e2 => emap (subExp (subShift s) e1) (subExp s e2)
  | efilter _ e1 e2 => efilter (subExp (subShift s) e1) (subExp s e2)
  end.

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

Fixpoint envDenote G : Type :=
  match G with
  | nil => unit
  | t :: G => prodT (tyDenote t) (envDenote G)
  end.

Fixpoint getVar G t (v : var G t) : envDenote G -> tyDenote t :=
  match v with
  | zvar _ _ => fun se => fst se
  | svar _ _ _ v => fun se => getVar v (snd se)
  end.

(* An interpreter *)
Fixpoint expDenote G t (e : exp G t) : envDenote G -> tyDenote t :=
  match e with
  | evar _ x => getVar x
  | econst n => fun _ => n
  | etrue => fun _ => true
  | efalse => fun _ => false
  | eplus e1 e2 => fun s => (expDenote e1 s) + (expDenote e2 s)
  | enil _ => fun _ => nil
  | econs _ e1 e2 => fun s => (expDenote e1 s) :: (expDenote e2 s)
  | elet _ _ e el =>
    fun s => expDenote el ((expDenote e s), s)
  | eappend _ e1 e2 => fun s => app (expDenote e1 s) (expDenote e2 s)
  | emap _ _ ef e =>
    fun s => let f := fun x => expDenote ef (x, s)
             in map f (expDenote e s)
  | efilter _ ef e =>
    fun s => let f := fun x => expDenote ef (x, s)
             in filter f (expDenote e s)
  end.

Eval compute in (expDenote app_prog) ().
Eval compute in (expDenote let_ex) ().
Eval compute in (expDenote inc) ().


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

Print nested_map.

Eval simpl in subExp {| econst 10; econst 20 |} (eplus (evar zvar) (evar (svar zvar))).

Example nested_map' : exp nil (TList TNat) :=
  emap (eplus (econst 3) (evar zvar))
  (emap (eplus (evar zvar) (econst 10)) [| econst 1 ; econst 2 ; econst 3 |]).

Example f1 : exp (TNat :: nil) (TList TNat) := (econs (evar zvar) enil).
Example f2 : exp (TNat :: nil) TNat := (eplus (evar zvar) (econst 10)).

Check (subExp {| f2 |} (shiftExp _ f1)).

Eval simpl in expDenote (emap f1 (emap f2 [| econst 10; econst 20; econst 30 |])).
Eval simpl in expDenote (emap (subExp {| f2 |} (shiftExp _ f1)) [| econst 10; econst 20; econst 30 |]).

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
    Ev e1 v1 -> Ev e2 v2 -> CApp v1 v2 v -> Ev (eappend e1 e2) v
| EvPlus : forall (e1 e2 : exp nil TNat) n1 n2,
    Ev e1 (vconst n1) -> Ev e2 (vconst n2) -> Ev (eplus e1 e2) (vconst (n1 + n2)).

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
    dependent destruction H.
    rewrite 
Qed.

  