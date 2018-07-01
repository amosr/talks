(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require GHC.Base.
Require GHC.Num.
Require Replicate.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Element a : Type := E : a -> GHC.Num.Int -> Element a.

Definition Encoded a :=
  (list (Element a))%type.

Arguments E {_} _ _.

Definition elementCount {a} (arg_0__ : Element a) :=
  let 'E _ elementCount := arg_0__ in
  elementCount.

Definition elementValue {a} (arg_0__ : Element a) :=
  let 'E elementValue _ := arg_0__ in
  elementValue.
(* Midamble *)

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

Require BinInt.
Require Import Omega.

Ltac termination_Z_to_nat :=
  match goal with
  | H : _ |- _ => try apply Z.ltb_lt in H
  end; intros; apply Z2Nat.inj_lt; omega.


(* Converted value declarations: *)

Definition consEncoded {a} `{GHC.Base.Eq_ a} : a -> Encoded a -> Encoded a :=
  fun a es =>
    match es with
    | nil => cons (E a #1) nil
    | cons e es =>
        if elementValue e GHC.Base.== a : bool
        then cons (let 'E elementValue_2__ elementCount_3__ := e in
                   E elementValue_2__ (elementCount e GHC.Num.+ #1)) es else
        (cons (E a #1) (cons e es))
    end.

Definition encode {a} `{GHC.Base.Eq_ a} : list a -> Encoded a :=
  fix encode as_
        := match as_ with
           | nil => nil
           | cons a as' => consEncoded a (encode as')
           end.

Definition decode {a} : Encoded a -> list a :=
  fix decode es
        := match es with
           | nil => nil
           | cons e es' =>
               Coq.Init.Datatypes.app (Replicate.replicate (elementCount e) (elementValue e))
                                      (decode es')
           end.

(* External variables:
     bool cons list nil Coq.Init.Datatypes.app GHC.Base.Eq_ GHC.Base.op_zeze__
     GHC.Num.Int GHC.Num.fromInteger GHC.Num.op_zp__ Replicate.replicate
*)
