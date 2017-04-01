Require Import Bool Arith List.
Require Import Coq.Program.Equality.
Load syntax.
Set Implicit Arguments.
Set Asymmetric Patterns.

Example let_ex : Exp TNat := fun _ =>
    elet (econst 10) (fun x => eplus (econst 32) (evar x)).

Example app_prog : Exp (TList TNat) := fun _ =>
    eappend (econs (econst 0) enil) (econs (econst 1) enil).

Example nested_map : Exp (TList TNat) :=
  fun _ => emap (fun x => eplus (econst 3) (evar x))
                (emap (fun x => eplus (evar x) (econst 10)) [| econst 1 ; econst 2 ; econst 3 |]).

Example flat_map : Exp (TList TNat) := fun _ =>
  emap (fun x => eplus (econst 3) (eplus (evar x) (econst 10)))
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
Fixpoint expDenote t (e : exp tyDenote t) : tyDenote t :=
  match e with
  | evar _ x => x
  | econst n => n
  | etrue => true
  | efalse => false
  | eplus e1 e2 => (expDenote e1) + (expDenote e2)
  | enil _ => nil
  | econs _ e1 e2 => (expDenote e1) :: (expDenote e2)
  | elet _ _ e el => expDenote (el (expDenote e))
  | eappend _ e1 e2 => app (expDenote e1) (expDenote e2)
  | emap _ _ ef e => (map (fun x => expDenote (ef x)) (expDenote e))
  end.

Definition ExpDenote t (E : Exp t) : tyDenote t :=
  expDenote (E tyDenote).

Eval compute in (ExpDenote app_prog).
Eval compute in (ExpDenote let_ex).

(* Substitute ef' for all occurences of x in ef *)

Lemma append_assoc : forall t (e1 e2 e3: exp tyDenote (TList t)),
    expDenote (eappend (eappend e1 e2) e3) =
    expDenote (eappend e1 (eappend e2 e3)).
Proof.
  intros.
  simpl.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Example dummy_proof : ExpDenote nested_map = ExpDenote flat_map.
simpl.
reflexivity.
Qed.

(* map f (map g) xs = map (f o g) xs
 * replace all occurences of x in f by result of g
 *)
 
  