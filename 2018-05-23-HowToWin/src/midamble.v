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

