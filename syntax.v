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
| emap : forall G t1 t2, exp (t1 :: G) t2 -> exp G (TList t1) ->exp G (TList t2).

Arguments econst [G].
Arguments etrue [G].
Arguments efalse [G].
Arguments enil [G t].

Notation "[| |]" := enil.
Notation "[| x |]" := (econs x nil).
Notation "[| x ; y ; .. ; z |]" := (econs x (econs y .. (econs z enil) ..)).
Notation "[| x ; .. ; y |]" := (econs x .. (econs y enil) ..).

(* Intrinsically typed values as well *)
Inductive val : ty -> Type :=
| vtrue : val TBool
| vfalse : val TBool
| vconst : nat -> val TNat
| vnil : forall t, val (TList t)
| vcons : forall t, val t -> val (TList t) -> val (TList t).