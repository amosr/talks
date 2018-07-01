Require Import List.

Lemma map_app_distr:
  forall A B
        (f : A -> B)
        (xs ys : List A),
    map f (append xs ys)
  = append (map f xs) (map f ys).
Proof.
 induction xs; intros; auto.
  simpl.
  rewrite IHxs.
  auto.
Qed.
