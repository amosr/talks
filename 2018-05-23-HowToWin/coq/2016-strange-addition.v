(* A strange way to specify addition. *)

Require Import Omega.

Locate "+".
Print Init.Nat.add.
Print nat.

Inductive added
  : nat -> nat -> nat -> Prop :=
| add_z: added 0 0 0
| add_l: forall m n r,
    added m n r
 -> added (S m) n (S r)
| add_r: forall m n r,
    added m n r
 -> added m (S n) (S r).


Lemma added_r:
  forall r,
  added 0 r r.
Proof.
Admitted.

Lemma added_plus:
  forall m n r,
  added m n r -> m + n = r.
Proof.
Admitted.

Lemma plus_added:
  forall m n r,
  m + n = r -> added m n r.
Proof.
Admitted.
