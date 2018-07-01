Require Import Replicate.

Require Coq.Init.Datatypes.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

Require Import Coq.Lists.List.
Import ListNotations.

Import BinInt.

Check replicate.

Theorem replicate_nil:
  forall
    (A : Type)
    (a : A),
  replicate (Z.of_nat 0) a = [].
Proof.
 eauto.
Qed.

Theorem replicate_cons:
  forall
    (A : Type)
    (n : nat)
    (a : A),
  replicate (Z.of_nat (S n)) a = a :: replicate (Z.of_nat n) a.
Proof.
  (* TODO!!!*)
Admitted.