Set Implicit Arguments.
Set Asymmetric Patterns.

Inductive bool : Set := true : bool | false : bool.

Definition and (b1 b2 : bool) : bool :=
  match b1 with
  | false => false
  | true => b2
  end.

Inductive list (T : Set) : Set :=
| nil : list T
| cons : T -> list T -> list T.

Arguments nil [T].
Arguments cons [T].

Fixpoint map (T T' : Set) (f : T -> T') (ls : list T) : list T' :=
  match ls with
  | nil => nil
  | cons x ls' => cons (f x) (map f ls')
  end.

Fixpoint filter (T : Set) (p : T -> bool) (ls : list T) : list T :=
  match ls with
  | nil => nil
  | cons x ls' => if p x then cons x (filter p ls') else filter p ls'
  end.

Theorem map_fusion : forall (T T' T'' : Set) (f : T' -> T'')
                            (g : T -> T') (ls : list T),
    map f (map g ls) = map (fun x => f (g x)) ls.
  induction ls. reflexivity.
  simpl. rewrite <- IHls. reflexivity.
Qed.

Lemma and_true_r : forall b : bool,
    and b true = b.
  intros.
  destruct b; reflexivity.
Qed.

Lemma and_false_r : forall b : bool,
    and b false = false.
  intros.
  destruct b; reflexivity.
Qed.

Lemma filter_fusion : forall (T : Set) (p q : T -> bool)
                             (ls : list T),
    filter p (filter q ls) = filter (fun x => and (p x) (q x)) ls.
  induction ls. reflexivity. simpl.
  destruct (q t); simpl.
  rewrite IHls. rewrite (and_true_r (p t)).
  reflexivity.
  rewrite (and_false_r (p t)). rewrite IHls.
  reflexivity.
Qed.


