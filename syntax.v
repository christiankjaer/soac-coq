Inductive ty : Type :=
| TBool : ty
| TNat : ty
| TList : ty -> ty.

Definition env := list ty.

Inductive var : env -> ty -> Type :=
| zvar : forall G t, var (t :: G) t
| svar : forall G t t', var G t -> var (t' :: G) t.

Arguments zvar [G t].
Arguments svar [G t t'].

(* Intrinsically typed expression syntax *)
Inductive exp G : ty -> Type :=
| evar : forall t, var G t -> exp G t
| etrue : exp G TBool
| efalse : exp G TBool
| econst : nat -> exp G TNat
| eplus : exp G TNat -> exp G TNat -> exp G TNat
| enil : forall t, exp G (TList t)
| econs : forall t, exp G t -> exp G (TList t) -> exp G (TList t)
| elet : forall t1 t2, exp G t1 -> exp (t1 :: G) t2 -> exp G t2
| eappend : forall t, exp G (TList t) -> exp G (TList t) -> exp G (TList t)
| emap : forall t1 t2, exp (t1 :: G) t2 -> exp G (TList t1) -> exp G (TList t2)
| efilter : forall t1, exp (t1 :: G) TBool -> exp G (TList t1) -> exp G (TList t1).

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