Require Import Bool Arith List.
Set Implicit Arguments.
Set Asymmetric Patterns.

(* Adam Chlipalas heterogeneous list implementation (magic inside)
 * Useful for De Bruijn indices
 *)
Section hlist.
  Variable A : Type.
  Variable B : A -> Type.

  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons : forall (x : A) (ls : list A), B x -> hlist ls -> hlist (x :: ls).

  Variable elm : A.

  Inductive member : list A -> Type :=
  | HFirst : forall ls, member (elm :: ls)
  | HNext : forall x ls, member ls -> member (x :: ls).

  Fixpoint hget ls (mls : hlist ls) : member ls -> B elm :=
    match mls with
    | HNil
      => fun mem =>
           match mem in member ls'
                 return (match ls' with
                         | nil => B elm
                         | _ :: _ => unit
                         end) with
           | HFirst _ => tt
           | HNext _ _ _ => tt
           end
    | HCons _ _ x mls'
      => fun mem =>
           match mem in member ls'
                 return (match ls' with
                         | nil => Empty_set
                         | x' :: ls'' =>
                           B x' -> (member ls'' -> B elm)
                           -> B elm
                         end) with
           | HFirst _ => fun x _ => x
           | HNext _ _ mem' => fun _ get_mls' => get_mls' mem'
           end x (hget mls')
    end.
  
End hlist.

Arguments HNil [A B].
Arguments HCons [A B x ls].

Arguments HFirst [A elm ls].
Arguments HNext [A elm x ls].

Inductive ty : Type :=
| TBool : ty
| TNat : ty
| TList : ty -> ty.

(* Intrinsically typed expression syntax *)
Inductive exp : list ty -> ty -> Type :=
| evar : forall G t, member t G -> exp G t
| etrue : forall G, exp G TBool
| efalse : forall G, exp G TBool
| econst : forall G, nat -> exp G TNat
| eplus : forall G, exp G TNat -> exp G TNat -> exp G TNat
| enil : forall G t, exp G (TList t)
| econs : forall G t, exp G t -> exp G (TList t) -> exp G (TList t)
| elet : forall G t1 t2, exp G t1 -> exp (t1 :: G) t2 -> exp G t2
| eappend : forall G t, exp G (TList t) -> exp G (TList t) -> exp G (TList t)
| emap : forall G t1 t2, exp G (TList t1) -> exp (t1 :: G) t2 -> exp G (TList t2).

Arguments econst [G].
Arguments etrue [G].
Arguments efalse [G].
Arguments enil [G].

(* Intrinsically typed values as well *)
Inductive val : ty -> Type :=
| vtrue : val TBool
| vfalse : val TBool
| vconst : nat -> val TNat
| vnil : forall t, val (TList t)
| vcons : forall t, val t -> val (TList t) -> val (TList t).

Example inc : exp nil (TList TNat) :=
  emap (econs (econst 4) (enil TNat)) (eplus (evar HFirst) (econst 3)).

Example let_ex : exp nil TNat :=
  elet (econst 42) (eplus (evar HFirst) (econst 10)).

Example app_prog : exp nil (TList TNat) := eappend (econs (econst 0) (enil TNat)) (econs (econst 1) (enil TNat)).

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
  | emap _ _ _ e ef =>
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

(* map f (map g) xs = map (f o g) xs
 * replace all occurences of x in f by result of g
 *)

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
| EvNil : forall t, Ev (enil t) (vnil t)
| EvCons : forall t (e1 : exp nil t) (e2 : exp nil (TList t))
                  (v1 : val t) (v2 : val (TList t)),
    Ev e1 v1 -> Ev e2 v2 -> Ev (econs e1 e2) (vcons v1 v2)
| EvAppend : forall t (e1 : exp nil (TList t)) (e2 : exp nil (TList t)) v1 v2 v,
    Ev e1 v1 -> Ev e2 v2 -> CApp v1 v2 v -> Ev (eappend e1 e2) v.

Example ev_example :
  Ev etrue vtrue.
apply EvTrue.
Qed.

Require Import Coq.Program.Equality.

(* CApp is deterministic *)
Lemma capp_determ : forall t (v1 v2 v3 v4 : val (TList t)),
    CApp v1 v2 v3 -> CApp v1 v2 v4 -> v3 = v4.
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