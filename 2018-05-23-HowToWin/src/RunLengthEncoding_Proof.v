Require Import RunLengthEncoding.
Require Import Replicate_Proof.

Require Coq.Init.Datatypes.
Require GHC.Base.
Require GHC.List.
Require GHC.Num.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

Require Import Coq.Lists.List.
Import ListNotations.
Import BinInt.

(* This probably exists elsewhere in hs-to-coq? *)
Axiom eq_eq : forall (A : Type)
    (eq_dict : GHC.Base.Eq_ A) (x y : A),
  _GHC.Base.==_ x y = true 
  <->
  x = y.


Theorem consEncoded_ok
  (A : Type)
  (eq_dict : GHC.Base.Eq_ A)
  (a : A)
  (xs : Encoded A)
  (POS : Forall (fun e => (elementCount e > 0)%Z) xs):

  decode (consEncoded a xs) = a :: (decode xs).
Proof.
 induction xs; eauto.
 destruct a0 as [eValue eCount]; simpl.
 destruct (_GHC.Base.==_ eValue a) eqn:EQ.
  simpl.

  (* TODO: apply replicate_cons_spec *)
  admit.

  eauto.
Admitted.

Theorem encode_positive
  (A : Type)
  (eq_dict : GHC.Base.Eq_ A)
  (inputs : list A):
    Forall (fun e => (elementCount e > 0)%Z) (encode inputs).
Proof.
  induction inputs; simpl; auto.

  unfold consEncoded.
  destruct (encode inputs) eqn:encode_inputs.
    constructor. simpl. Omega.omega.
    auto.
  simpl.
  inversion IHinputs.
    subst.
  destruct (_GHC.Base.==_ _ _).
    destruct e. simpl.
    constructor. simpl in *. Omega.omega.
    auto.

  constructor.
    simpl. Omega.omega.
    auto.
Qed.

Lemma roundtrip
  (A : Type)
  (eq_dict : GHC.Base.Eq_ A)
  (inputs : list A):
    decode (encode inputs) = inputs.
Proof.
  induction inputs; simpl; auto.
    rewrite consEncoded_ok.
    rewrite IHinputs.
    auto.
   apply encode_positive.
Qed.