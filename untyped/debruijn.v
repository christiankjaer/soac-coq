Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List
Require Import Coq.Logic.FunctionalExtensionality.

Inductive ty : Type :=
| TBool : ty
| TNat : ty
| TList : ty -> ty.

Inductive exp : Type :=
| evar : nat -> exp
| etrue : exp
| efalse : exp
| econst : nat -> exp
| eplus : exp -> exp -> exp
| enil : exp
| econs : exp -> exp -> exp
| eappend : exp -> exp -> exp
| emap : exp -> exp -> exp.

Inductive val : Type :=
| vtrue : val
| vfalse : val
| vconst : nat -> val
| vnil : val
| vcons : val -> val -> val.

Definition context := list ty.

Inductive has_type : context -> exp -> ty -> Prop :=
| tvar : forall G x T,
    G x = Some T -> has_type G (evar x) T
| ttrue : forall G, has_type G etrue TBool
| tfalse : forall G, has_type G efalse TBool
| tconst : forall G n, has_type G (econst n) TNat
| tplus : forall G e1 e2, has_type G e1 TNat ->
                          has_type G e2 TNat ->
                          has_type G (eplus e1 e2) TNat
| tnil : forall G t, has_type G enil (TList t)
| tcons : forall G e e' t,
    has_type G e t -> has_type G e' (TList t) ->
    has_type G (econs e e') (TList t)
| tappend : forall G e e' t,
    has_type G e (TList t) -> has_type G e' (TList t) ->
    has_type G (eappend e e') (TList t)
| tmap : forall G x e el t t',
    has_type (update G x t) e t' -> has_type G el (TList t) ->
    has_type G (emap x e el) (TList t').

Inductive val_has_type : val -> ty -> Prop :=
| vttrue : val_has_type vtrue TBool
| vtfalse : val_has_type vfalse TBool
| vtconst : forall n, val_has_type (vconst n) TNat
| vtnil : forall t, val_has_type vnil (TList t)
| vtcons : forall v v' t,
    val_has_type v t -> val_has_type v' (TList t) ->
    val_has_type (vcons v v') (TList t).

Definition env := partial_map val.

Inductive eval : env -> exp -> val -> Prop :=
| ev_var : forall G x v,
    G x = Some v -> eval G (evar x) v
| ev_true : forall G, eval G etrue vtrue
| ev_false : forall G, eval G efalse vfalse
| ev_const : forall G n, eval G (econst n) (vconst n)
| ev_plus : forall G e1 e2 n1 n2,
    eval G e1 (vconst n1) -> eval G e2 (vconst n2) ->
    eval G (eplus e1 e2) (vconst (n1 + n2))
| ev_nil : forall G, eval G enil vnil
| ev_cons : forall G e1 e2 v1 v2, eval G e1 v1 -> eval G e2 v2 ->
                                  eval G (econs e1 e2) (vcons v1 v2).

Definition x := (Id "x").
Definition y := (Id "y").
Definition z := (Id "z").
Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

Hint Constructors has_type.

Example typing :
  has_type empty (eplus (econst 10) (econst 20)) TNat.
Proof.
  auto.
Qed.

Hint Immediate tplus.

Example typing1 :
  has_type empty (emap x (eplus (evar x) (econst 10)) (econs (econst 10) (econs (econst 20) enil))) (TList TNat).
Proof.
  eapply tmap.
  apply tplus.
  apply tvar.
  rewrite update_eq.
  reflexivity.
  apply tconst.
  auto.
Qed.

(* substitute x with s in t *)
Fixpoint subst (x:id) (s:exp) (e:exp) : exp :=
  match e with
  | evar x' => if beq_id x x' then s else e
  | etrue => etrue
  | efalse => efalse
  | econst n => econst n
  | eplus e1 e2 => eplus (subst x s e1) (subst x s e2)
  | enil => enil
  | econs e1 e2 => econs (subst x s e1) (subst x s e2)
  | eappend e1 e2 => eappend (subst x s e1) (subst x s e2)
  | emap x' e1 e2 => emap x' (if beq_id x x' then e1 else (subst x s e1))
                          (subst x s e2)
  end.

Inductive appears_free_in : id -> exp -> Prop :=
| afi_var : forall x, appears_free_in x (evar x)
| afi_plus1 : forall x e1 e2, appears_free_in x e1 -> appears_free_in x (eplus e1 e2)
| afi_plus2 : forall x e1 e2, appears_free_in x e2 -> appears_free_in x (eplus e1 e2)
| afi_cons1 : forall x e1 e2, appears_free_in x e1 -> appears_free_in x (econs e1 e2)
| afi_cons2 : forall x e1 e2, appears_free_in x e2 -> appears_free_in x (econs e1 e2)
| afi_app1 : forall x e1 e2, appears_free_in x e1 -> appears_free_in x (eappend e1 e2)
| afi_app2 : forall x e1 e2, appears_free_in x e2 -> appears_free_in x (eappend e1 e2)
| afi_map1 : forall x y e1 e2, x <> y -> appears_free_in x e1 -> appears_free_in x (emap y e1 e2)
| afi_map2 : forall x e1 e2, appears_free_in x e2 -> appears_free_in x (emap x e1 e2).
                                                                      

Lemma free_in_context : forall x e T G,
    appears_free_in x e ->
    has_type G e T ->
    exists T', G x = Some T'.
  intros. generalize dependent G.
  generalize dependent T.
  induction H; intros;
    try (inversion H0; eauto);
    inversion H1;
    subst;
    try (match goal with
         | [ H : has_type _ _ _ |- _ ] => apply IHappears_free_in in H;
                                          rewrite update_neq in H
                                                                  
         end);
    auto.
Qed.

Lemma empty_is_empty : forall A (x : id), (empty : partial_map A) x = None.
  Proof.
    intros.
    unfold empty.
    unfold t_empty.
    reflexivity.
Qed.

Lemma ev_preserves_type : forall e v T,
    has_type empty e T -> eval empty e v -> val_has_type v T.
  intros.
  generalize dependent H0.
  induction H; intros; inversion H0; subst.
  rewrite empty_is_empty in H3.
  inversion H3.
  constructor.
  constructor.
  constructor.
  








  


Lemma subst_preserves_type : forall G x T' e e' T,
    has_type (update G x T') e T ->
    has_type empty e' T' ->
    has_type G (subst x e' e) T.
Proof.
  intros G x T' e e' T.
  generalize dependent G. generalize dependent T.
  induction e; intros T G H; inversion H;
    subst; simpl.
  destruct (beq_id x i).


  
Definition map_fusion (e : exp) : exp :=
  match e with
  | emap x f list =>
    match list with
    | emap y g list' => emap y (subst x g f) list'
    | _ => e
    end
  | _ => e
  end.

Example nested_map := emap x (eplus (evar x) (econst 10)) (emap x (eplus (econst 5) (evar x)) (econs (econst 10) (econs (econst 20) enil))).

Eval simpl in (map_fusion nested_map).

Lemma map_fusion_type_preservation : forall e t, has_type empty e t -> has_type empty (map_fusion e) t.
  intros.
  induction e;
    destruct t;
    try (unfold map_fusion; assumption).
  inversion H.
  inversion H.
  



  

  

  

  

