Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Autosubst.Autosubst.

Inductive ty : Type :=
| TBool : ty
| TNat : ty
| TList : ty -> ty.

Inductive term : Type :=
| evar (x : var)
| etrue
| efalse
| econst (n : nat)
| eplus (e1 e2 : term)
| enil
| econs (e1 e2 : term)
| elet (e1 : term) (e2 : {bind term})
| emap (e1 : {bind term}) (e2 : term).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

Inductive val : Type :=
| vtrue
| vfalse
| vconst (n : nat)
| vnil
| vcons (v1 v2 : val).

Definition context := var -> ty.

Inductive has_type (G : context) : term -> ty -> Prop :=
| tvar x T : G x = T -> has_type G (evar x) T
| ttrue : has_type G etrue TBool
| tfalse : has_type G efalse TBool
| tconst n : has_type G (econst n) TNat
| tplus e1 e2 : has_type G e1 TNat ->
                has_type G e2 TNat ->
                has_type G (eplus e1 e2) TNat
| tnil T : has_type G enil (TList T)
| tcons e1 e2 T : has_type G e1 T ->
                  has_type G e2 (TList T) ->
                  has_type G (econs e1 e2) (TList T)
| tlet e1 e2 T1 T2 : has_type G e1 T1 ->
                     has_type (T1 .: G) e2 T2 ->
                     has_type G (elet e1 e2) T2
| tmap e1 e2 T1 T2 : has_type (T1 .: G) e1 T2 ->
                     has_type G e2 (TList T1) ->
                     has_type G (emap e1 e2) (TList T2).


Inductive val_has_type : val -> ty -> Prop :=
| vttrue : val_has_type vtrue TBool
| vtfalse : val_has_type vfalse TBool
| vtconst n : val_has_type (vconst n) TNat
| vtnil t : val_has_type vnil (TList t)
| vtcons v v' t : val_has_type v t ->
                   val_has_type v' (TList t) ->
                   val_has_type (vcons v v') (TList t).



Definition env := var -> val.

Inductive eval (R : env) : term -> val -> Prop :=
| ev_var x v : R x = v -> eval R (evar x) v
| ev_const n : eval R (econst n) (vconst n)
| ev_true : eval R etrue vtrue
| ev_false : eval R etrue vtrue
| ev_plus e1 e2 n1 n2 : eval R e1 (vconst n1) ->
                        eval R e1 (vconst n2) ->
                        eval R (eplus e1 e2) (vconst (n1 + n2))
| ev_nil : eval R enil vnil
| ev_cons e1 e2 v1 v2 : eval R e1 v1 -> eval R e2 v2 -> eval R (econs e1 e2) (vcons v1 v2).

Definition context_env_agree (G : context) (R : env) := forall x, val_has_type (R x) (G x).

Lemma ev_pres_type T G R e v : context_env_agree G R ->
                               has_type G e T ->
                               eval R e v ->
                               val_has_type v T.
Proof.
  unfold context_env_agree.
  induction 3;
  inversion H0;
  subst;
  try eapply H;
  constructor.
  
Qed.
  


Definition map_fusion (e : term) : term :=
  match e with
  | emap f list =>
    match list with
    | emap g list' => emap f.[g/] list'
    | _ => e
    end
  | _ => e
  end.

Example nested_map := emap (eplus (evar 0) (econst 10)) (emap (eplus (econst 5) (evar 0)) (econs (econst 10) (econs (econst 20) enil))).

Eval simpl in (map_fusion nested_map).

Lemma type_subst G e1 e2 T0 T1 T2 : has_type (T1 .: G) e1 T2 ->
                                    has_type (T0 .: G) e2 T1 ->
                                    has_type (T0 .: G) e1.[e2/] T2.
  Admitted.

Lemma map_fusion_type_preservation G e T : has_type G e T -> has_type G (map_fusion e) T.
  intros.
  induction e;
  try (simpl; assumption).
  destruct H;
  try (simpl; constructor; repeat eauto).
  simpl. eapply tlet. eauto. auto.
  destruct e2;
    try (simpl;
         eapply tmap;
         eassumption;
         eassumption).
  simpl.
  inversion H0.
  subst.
  eapply tmap.
  eapply type_subst.
  eauto.
  eauto.
  auto.
Qed.
  
  