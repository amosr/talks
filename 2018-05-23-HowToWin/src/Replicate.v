(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require BinInt.
Require GHC.Base.
Require GHC.Num.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* No type declarations to convert. *)
(* Midamble *)

Require Import Omega.

(* How to prove
     0 <? num = true
  -> Z.to_nat (num - 1) < Z.to_nat num
*)
Ltac termination_Z_to_nat :=
  Program.Tactics.program_simpl;
  simpl;
  (* convert (0 <? num = true) to (0 < num) so omega can use it *)
  match goal with
  | H : _ |- _ => try apply Z.ltb_lt in H
  end;
  intros; apply Z2Nat.inj_lt; omega.


(* Converted value declarations: *)

Program Fixpoint replicate {a} (num : GHC.Num.Int) (aa : a)
                           {measure (BinInt.Z.to_nat num)} : list a
                   := if Bool.Sumbool.sumbool_of_bool (num GHC.Base.> #0)
                      then cons aa (replicate (num GHC.Num.- #1) aa) else
                      nil.
Solve Obligations with (termination_Z_to_nat).

(* External variables:
     Bool.Sumbool.sumbool_of_bool cons list nil BinInt.Z.to_nat GHC.Base.op_zg__
     GHC.Num.Int GHC.Num.fromInteger GHC.Num.op_zm__
*)
