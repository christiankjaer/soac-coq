Set Implicit Arguments.
Set Asymmetric Patterns.

Definition compose (A B C : Set) (f : B -> C) (g : A -> B) := fun x => f (g x).
Notation "f 'o' g" := (compose f g) (at level 80, right associativity).

Inductive option (T : Set) : Set :=
| SOME : T -> option T
| NONE : option T.

Definition compose' (A B C : Set)(f : B -> option C) (g : A -> option B) : (A -> option C) :=
  fun a => match g a with
           | NONE => NONE C
           | SOME b => f b
           end.

Notation "f 'oo' g" := (compose' f g) (at level 80, right associativity).

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

Notation "[]" := (nil).
Notation "[ a ]" := (cons a nil).
Notation "[ a ; b ; .. ; c ]" := (cons a (cons b .. (cons c nil) ..)).
Notation "[ a ; .. ; b ]" := (cons a .. (cons b nil) ..).

Fixpoint map (T T' : Set) (f : T -> T') (ls : list T) : list T' :=
  match ls with
  | [] => []
  | cons x ls' => cons (f x) (map f ls')
  end.

Fixpoint filter (T : Set) (p : T -> bool) (ls : list T) : list T :=
  match ls with
  | [] => []
  | cons x ls' => if p x then cons x (filter p ls') else filter p ls'
  end.

Fixpoint mapPartial (T T' : Set) (f : T -> option T') (ls : list T) : list T' :=
  match ls with
  | nil => nil
  | cons x ls' => match (f x) with
                  | NONE => mapPartial f ls'
                  | SOME y => cons y (mapPartial f ls')
                  end
  end.

Theorem map_fusion : forall (T T' T'' : Set) (f : T' -> T'')
                            (g : T -> T') (ls : list T),
    map f (map g ls) = map (f o g) ls.
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

Lemma mapPartial_fusion : forall (T T' T'' : Set) (f : T' -> option T'')
                                 (g : T -> option T') (ls : list T),
    ((mapPartial f) o (mapPartial g)) ls = mapPartial (f oo g) ls.
