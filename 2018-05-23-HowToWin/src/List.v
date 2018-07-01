(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* No imports to convert. *)

(* Converted type declarations: *)

Inductive List a : Type := Nil : List a |  Cons : a -> (List a) -> List a.

Arguments Nil {_}.

Arguments Cons {_} _ _.
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

Definition append {a} : List a -> List a -> List a :=
  fix append as_ bs
        := match as_ with
           | Nil => bs
           | Cons a as' => Cons a (append as' bs)
           end.

Definition map {a} {b} : (a -> b) -> List a -> List b :=
  fix map f as_
        := match as_ with
           | Nil => Nil
           | Cons a as' => Cons (f a) (map f as')
           end.
