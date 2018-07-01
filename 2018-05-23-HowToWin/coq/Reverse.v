Set Implicit Arguments.

Inductive List (A : Type) :=
  | Nil : List A
  | Cons : A -> List A -> List A.






Fixpoint snoc (A : Type)
    (xs : List A) (tail : A) :=
  match xs with
  | Nil _ => Cons tail (Nil _)
  | Cons x xs' => Cons x (snoc xs' tail)
  end.

Fixpoint reverse (A : Type)
    (xs : List A) :=
  match xs with
  | Nil _ => Nil _
  | Cons x xs' => snoc (reverse xs') x
  end.






Theorem reverse_snoc
  (A  : Type)
  (x  : A)
  (xs : List A)
      : reverse (snoc xs x)
      = Cons x (reverse xs).
Proof.
Admitted.







Theorem reverse_reverse_involutive
  (A  : Type)
  (xs : List A)
      : reverse (reverse xs)
      = xs.
Proof.
Admitted.
