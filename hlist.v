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