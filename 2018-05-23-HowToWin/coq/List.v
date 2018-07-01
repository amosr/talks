Set Implicit Arguments.

Inductive List (A : Type) :=
  | Nil : List A
  | Cons : A -> List A -> List A.

Fixpoint append (A : Type) (xs ys : List A) :=
  match xs with
  | Nil _
    => ys
  | Cons x xs'
    => Cons x (append xs' ys)
  end.

Fixpoint map (A B : Type) (f : A -> B) (xs : List A) :=
  match xs with
  | Nil _
    => Nil _
  | Cons x xs'
    => Cons (f x) (map f xs')
  end.

Theorem append_nil
  (A  : Type)
  (ys : List A)
      : append (Nil _) ys = ys.
Proof.
 unfold append.
 reflexivity.

Restart.
 auto.
Qed.

Theorem append_cons
  (A      : Type)
  (x      : A)
  (xs ys  : List A)
          : append (Cons x xs) ys = Cons x (append xs ys).
Proof.
  unfold append at 1.
  fold append.
  reflexivity.

Restart.
 auto.
Qed.

Theorem map_app
  (A B    : Type)
  (f      : A -> B)
  (xs ys  : List A)
          : map f (append xs ys) = append (map f xs) (map f ys).
Proof.

  induction xs.
  * rewrite append_nil.
    unfold map at 2.
    rewrite append_nil.

    reflexivity.

  * unfold append; fold append.
    unfold map; fold map.
    unfold append; fold append.

    rewrite IHxs.
    reflexivity.

Restart.

 induction xs.
  * auto.
  * simpl.
    rewrite IHxs.
    auto.
Qed.

Print append_cons.

Fixpoint snoc (A : Type) (xs : List A) (tail : A) :=
  match xs with
  | Nil _ => Cons tail (Nil _)
  | Cons x xs' => Cons x (snoc xs' tail)
  end.

Fixpoint reverse (A : Type) (xs : List A) :=
  match xs with
  | Nil _ => Nil _
  | Cons x xs' => snoc (reverse xs') x
  end.


Theorem reverse_snoc
  (A  : Type)
  (x  : A)
  (xs : List A)
      : reverse (snoc xs x) = Cons x (reverse xs).
Proof.
 induction xs.
  * simpl.
    reflexivity.
  * simpl.
    rewrite IHxs.
    simpl.
    reflexivity.
Qed.

Theorem reverse_reverse_involutive
  (A  : Type)
  (xs : List A)
      : reverse (reverse xs) = xs.
Proof.
 induction xs.
  * simpl.
    reflexivity.
  * simpl.
    rewrite reverse_snoc.
    rewrite IHxs.
    reflexivity.
Qed.

