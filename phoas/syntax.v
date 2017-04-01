Inductive ty : Type :=
| TBool : ty
| TNat : ty
| TList : ty -> ty.

(* Intrinsically typed expression syntax *)
Section var.
  Variable var : ty -> Type.
  
  Inductive exp : ty -> Type :=
  | evar : forall t, var t -> exp t
  | etrue : exp TBool
  | efalse : exp TBool
  | econst : nat -> exp TNat
  | eplus : exp TNat -> exp TNat -> exp TNat
  | enil : forall t, exp (TList t)
  | econs : forall t, exp t -> exp (TList t) -> exp (TList t)
  | elet : forall t1 t2, exp t1 -> (var t1 -> exp t2) -> exp t2
  | eappend : forall t, exp (TList t) -> exp (TList t) -> exp (TList t)
  | emap : forall t1 t2, (var t1 -> exp t2) -> exp (TList t1) -> exp (TList t2).
End var.

Arguments evar [var t].
Arguments econst [var].
Arguments etrue [var].
Arguments efalse [var].
Arguments enil [var t].
Arguments emap [var t1 t2].
Arguments elet [var t1 t2].
Arguments eplus [var].
Arguments econs [var t].
Arguments eappend [var t].


Notation "[| |]" := enil.
Notation "[| x |]" := (econs x nil).
Notation "[| x ; y ; .. ; z |]" := (econs x (econs y .. (econs z enil) ..)).
Notation "[| x ; .. ; y |]" := (econs x .. (econs y enil) ..).

Definition Exp t := forall var, exp var t.

(* Intrinsically typed values as well *)
Inductive val : ty -> Type :=
| vtrue : val TBool
| vfalse : val TBool
| vconst : nat -> val TNat
| vnil : forall t, val (TList t)
| vcons : forall t, val t -> val (TList t) -> val (TList t).

Arguments vnil [t].
Arguments vcons [t].