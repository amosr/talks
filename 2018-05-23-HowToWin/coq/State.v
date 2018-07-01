

(*
newtype State s s' r = Build_State
  { runState :: (s -> (s',r) }
*)




Record State (S S' A : Type) := Build_State
  { runState : (S -> S' * A)
  }.


Definition returnS (S A : Type) : A -> State S S A.
Admitted.


Definition bindS (S S' S'' A B : Type)
   : State S S' A
  -> (A -> State S' S'' B)
  -> State S S'' B.
Admitted.







Definition returnS' (S A : Type) : A -> State S S A :=
  fun a =>
    Build_State _ _ _ (fun s => (s, a)).


Definition bindS' (S S' S'' A B : Type)
   : State S S' A
  -> (A -> State S' S'' B)
  -> State S S'' B :=
  fun sA sA_to_B =>
  Build_State _ _ _
  (fun s =>
     let (s',a) := runState _ _ _ sA s
     in runState _ _ _ (sA_to_B a) s'
  ).
