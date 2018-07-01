Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.

Inductive Values : list Set -> Type :=
  | Values'nil : Values []
  | Values'cons (A : Set) (AS : list Set) (a : A) : Values AS -> Values (A :: AS).


Inductive STRef : list Set -> Set -> Type :=
  | STRef'here (A : Set) (AS : list Set) : STRef (A :: AS) A
  | STRef'there (A B : Set) (AS : list Set) :
      STRef AS B -> STRef (A :: AS) B.

Inductive ST (AS AS' : list Set) (R : Type) :=
  | ST'mk : (Values AS -> Values AS' * R) -> ST AS AS' R.


Definition runST (s : list Set) (a : Set) (st :  ST [] s a) : a.
destruct st.
apply p.
constructor.
Defined.

Definition returnST s (a : Set) : a -> ST s s a.
constructor; auto.
Defined.

Print returnST.

Definition bindST (a b : Set) (s s' s'' : list Set) : ST s s' a -> (a -> ST s' s'' b) -> ST s s'' b.
intros.
destruct X.
intros; constructor.
intros.
apply p in X.
destruct X.
apply X0 in a0.
destruct a0.
apply p0 in v. eauto.
Defined.

Print bindST.

Definition newSTRef (a : Set) (s : list Set) : a -> ST s (a :: s) (STRef (a :: s) a).
repeat constructor; auto.
Defined.

Print newSTRef.


Definition readSTRef (a : Set) (s : list Set) : STRef s a -> ST s s a.
intros.
induction X.
constructor. intros.

inversion X; eauto.

destruct IHX.
constructor.
intros.
inversion X0.
apply p in X1.
destruct X1.
constructor; auto.
Defined.

Print readSTRef.



Definition writeSTRef (a : Set) (s : list Set) : STRef s a -> a -> ST s s unit.
intros.
constructor.
intros.
induction X0.
  inversion X.

inversion X.
repeat constructor; eauto.
repeat constructor; eauto.
Defined.

Print writeSTRef.
