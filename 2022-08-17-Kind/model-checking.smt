; # Model-checking techniques for reactive systems.
;
; This file is an SMT-lib script that model checks a simple streaming program.
; You can check it by installing an SMT solver such as Z3 and running:
;$ z3 bounds.smt
;
; I am working on an embedded domain-specific language for writing streaming
; control systems. I'm working on a model checker for it at the moment, and the
; goal is to eventually have a model checker and a compiler so that we can use
; it to implement and verify trustworthy control systems.
;
; The language itself is very strongly influenced by Lustre. There are already
; some good model checkers for Lustre, especially [Kind2](https://kind2-mc.github.io/kind2/),
; but I think that having an embedded language will help with expressing larger
; and more interesting programs. It's also similar to the Galois [Copilot](https://github.com/Copilot-Language/copilot)
; project, but with more focus on model checking. Copilot doesn't support
; contracts, which I think you really need to if you want to prove properties
; on larger systems.
; 
; A common fault check for control systems is to check whether a predicate has
; been true for some fixed, finite history of time. We call this `LastN(n, e)`
; for some integer `n` and stream of booleans `e`. This returns a new stream
; that is true whenever `e` has been true for the `n` most recent ticks,
; including now. We can implement `LastN` as a recursive function:
;
;> def LastN(n: Int, e: Stream[Bool]): Stream[Bool] = n match
;>   case 0 => True
;>   case 1 => e
;>   case _ => e && LastN(n - 1, fby(False, e))
;
; When `n` is zero, we are looking at an empty history, so the result is true.
; When `n` is one, we are looking at a single element of the stream history, so
; the result is just the current value (`e`). It gets more interesting when `n`
; is a natural number larger than one: we check whether the stream is currently
; true right now, and we check whether a delayed stream has been true for
; `n - 1` ticks. The expression `fby(False, e)` denotes a delayed stream that
; initially has the value `False`: given some input stream `[e_0, e_1, e_2,...]`
; the result `fby(False, e) = [False, e_0, e_1, e_2,...]`.
;
; We can also express a windowed mean, or "mean over last n values", in a
; similar way by recursively delaying the stream and adding the result:
;
;> def MeanN(n: Int, v: Stream[Int32]): Stream[Int32] =
;>   SumN(n, v) / n
;>
;> def SumN(n: Int, v: Stream[Int32]): Stream[Int32] = n match
;>   case 0 => 0
;>   case 1 => v
;>   case _ => v + SumN(n - 1, fby(0, v))
;
; For the model checking, we can also express properties in our embedded
; streaming language and then get the SMT solver to prove them. I will
; informally describe the hand translation as I'm still working on the
; implementation.
;
; Suppose we have an input stream that denotes an untrusted control input. We
; want to check that this input falls within the allowed bounds before we use
; it. The control input is a bit noisy too, so we need to do a bit of
; filtering to get rid of the noise as well. We want to prove that if the input
; has been within the bounds for some limited history, then the result coming
; from our low-pass filter will also be within the bounds.
;
; For simplicity, we just implement our low-pass filter using the windowed mean
; mentioned above, and we limit our history to two stream elements (the current
; and the previous). Our property looks something like:
;
;> val input: Stream[Int32] = local[Int32]
;> property {
;>   val HISTORY = 2
;>   LastN(HISTORY, input < MAXIMUM) ==> MeanN(HISTORY, input) < MAXIMUM
;> }
;
; Our language is an domain specific language embedded in Scala, so we
; automatically get the meta-language's standard evaluation rules. Those rules
; will inline the definition of LastN, MeanN, and so on, until we have an
; expression that is constructed from just primitive applications:
;
;> val input: Stream[Int32] = local[Int32]
;> property {
;>   input < MAXIMUM && fby(False, input < MAXIMUM) ==>
;>     ((input + fby(0, input)) / 2 < MAXIMUM)
;> }
;
; I've used the Scala syntax for expressions to represent the resulting
; program, but in actual execution it would be an abstract syntax tree that
; denotes the same expression.
;
; To make it easier to work with the program, we convert it into a regular
; structure called administrative normal form (ANF). To convert it to ANF we
; insert variable bindings for each operator application, until all of the
; arguments are either primitive values or variables:
;
;> val input: Stream[Int32] = local[Int32]
;> property {
;>   val input_in_bounds       = input < MAXIMUM
;>   val input_in_bounds_delay = fby(False, input_in_bounds)
;>   val last_in_bounds        = input_in_bounds && input_in_bounds_delay
;>
;>   val input_delay           = fby(0, input)
;>   val input_sum             = input + input_delay
;>   val mean                  = input_sum / 2
;>   val mean_in_bounds        = mean < MAXIMUM
;>
;>   last_in_bounds ==> mean_in_bounds
;> }
;
; Now that we have our program in a normalised form, we can start representing
; it inside the SMT solver.
;
; We don't really care what value MAXIMUM has, so we declare it as constant
; (non-streaming) integer with some unspecified value:
(declare-const MAXIMUM Int)

; ## Transition systems
;
; The SMT solver doesn't have a theory of streams, so we need to represent our
; streaming program in an encoding that the SMT solver understands. We'll do
; this by representing our streaming program as a transition system. The first
; step is to split out the stateful (streaming) bindings from the pure ones,
; and put all of the stateful ones in a State record.
; Our program only uses the streaming primitive `fby`; the bindings that use
; `fby` are stateful, while the others are pure.
; The State record has two fields: a boolean for the `input_in_bounds_delay`
; binding and an integer for the `input_delay` binding.
(declare-datatype State
  ((State
    (input_in_bounds_delay Bool)
    (input_delay           Int))))

; All of the other bindings are pure, so we put them in a different record. I
; call this the "row" record because it describes a "whole row" of streaming
; values at a particular instant in time.
; We include the input stream `input` too: it doesn't have a concrete
; definition so we don't need to give it a concrete state.
(declare-datatype Row
  ((Row
    (input           Int)
    (input_in_bounds Bool)
    (last_in_bounds  Bool)
    (input_sum       Int)
    (mean            Int)
    (mean_in_bounds  Bool))))

; Our transition system is an abstract description of how the state changes
; over time. As part of that abstract description, we need to describe the
; initial state that the system starts from. We define an `init` predicate
; that takes a state and returns true if the state is initial.
; To define this function, we look at each of the stateful bindings and use
; the initial value of the "followed-by" primitive. For
; `input_in_bounds_delay`, the definition is `fby(False, input_in_bounds)`,
; so the initial state for `input_in_bounds_delay` is false:
(define-fun init ((state State)) Bool
  (and
    (= (input_in_bounds_delay state) false)
    (= (input_delay           state) 0)))

; We define `init` as a predicate rather than a single value of type state,
; because in general there can be many possible initialisation states if some
; value is left undefined. In this case, however, the predicate describes a
; single state.

; We also define a "step" relation that describes how the state changes for
; each subsequent stream instant. The `step` relation takes a starting state
; and the row values containing the values of the pure bindings, and describes
; the "next" state (`stateX`).
; To come up with the definition, we look at the second parameter of the
; followed-by primitive. For binding `input_in_bounds_delay = fby(False, input_in_bounds)`,
; we define the new state to be the `input_in_bounds` variable. As `input_in_bounds`
; is a pure binding, we look it up inside the row.
(define-fun step ((state State) (row Row) (stateX State)) Bool
  (and
    (= (input_in_bounds_delay stateX) (input_in_bounds row))
    (= (input_delay           stateX) (input           row))))

; The next piece is the `extract` function which "extracts the pure bindings".
; It takes a state and the row and gives the pure bindings their meaning.
; We define this by looking at each of the pure bindings and applying the
; corresponding SMT-lib primitive.
(define-fun extract ((state State) (row Row)) Bool
  (and
    (= (input_in_bounds row) (< (input row) MAXIMUM))
    (= (last_in_bounds  row) (and (input_in_bounds row) (input_in_bounds_delay state)))
    (= (input_sum       row) (+ (input row) (input_delay state)))
    (= (mean            row) (/ (input_sum row) 2))
    (= (mean_in_bounds  row) (< (mean row) MAXIMUM))))

; As the final piece of our transition system, we define the property that we
; want to prove. This definition takes the values of the pure bindings and
; returns true when the property is satisfied.
(define-fun prop ((row Row)) Bool
  (=> (last_in_bounds row) (mean_in_bounds row)))

; We now have a transition system that lets us reason about our streaming
; program inside the SMT solver's logic. We want to prove that all of the
; states that the transition system can reach satisfy our property. To do this
; proof, we'll use induction over the sequence of steps of the system.
;
; To start with, we declare a starting state `state0` as well as its
; corresponding row for pure bindings `row0`. These variables do not have a
; concrete definition; the SMT solver is going to try and find a value that
; satisfies our SMT problem.
(declare-const state0 State)
(declare-const row0   Row)

; ## Induction
;
; For the inductive base case, we push the current assertion state onto the
; stack, then tell the SMT solver what specific problem we want it to solve.
; When we usually do induction, we state the base case as something like "for
; all initial states, the property holds". However, the SMT solver works with
; satisfiability problems, so we need to restate our problem as "does there
; exist an initial state that violates the property?"
(push)
; Find values for state0 and row0 such that...
; state0 describes an initial state; and
(assert (init    state0))
; the pure bindings have the right values; and
(assert (extract state0 row0))
; it violates the property.
(assert (not (prop row0)))

; Then we ask the SMT solver to find a counterexample. If our property holds,
; then we will get an _unsatisfiable_ result, because there is no
; counterexample. If our property doesn't hold, the result will be
; _satisfiable_.
(echo "inductive base case. expect unsat")
(check-sat)
(pop)

; We reset the state and then state the inductive step case. Usually, we would
; prove that "if we start in a good state and take a step, then the new state
; is also good". To state this as a satisfiability problem, we invert it to ask
; "does there exist a starting state and a successor state such that a good
; starting state steps to a bad state?"
(push)

; We declare variables for the successor state and row too. 
(declare-const state1 State)
(declare-const row1   Row)

; Find values for state0, row0, state1, row1, such that...
; the pure bindings in row0 correspond to state state0; and
(assert (extract state0 row0))
; the starting state state0 takes a step to successor state1; and
(assert (step    state0 row0 state1))
; the pure bindings in row1 correspond to the successor state; and
(assert (extract state1 row1))
; the property holds in the starting state's corresponding pure values; and
(assert (prop row0))
; the successor state's corresponding pure values violate the property.
(assert (not (prop row1)))

; We ask the SMT solver to find a satisfying solution. If our property holds,
; we will get an unsatisfiable result, because there is no step that violates
; our property.
(echo "inductive step case. expect unsat")
(check-sat)
; z3 says: unsat
(pop)

; Both of the problems were unsatisfiable, so we have successfully proved the
; inductive property: that is, all executions of our transition system satisfy
; the property:
;
;>  LastN(HISTORY, input < MAXIMUM) ==> MeanN(HISTORY, input) < MAXIMUM
;
; where HISTORY = 2 and input is a stream of integers.


; ## K-induction
; What if we want to look further behind, with HISTORY = 3? The property is
; becomes `LastN(3, input < MAXIMUM) ==> MeanN(3, input) < MAXIMUM`, which
; normalises to the following program:

;> val input: Stream[Int32] = local[Int32]
;> property {
;>   val input_in_bounds        = input < MAXIMUM
;>   val input_in_bounds_delay1 = fby(False, input_in_bounds)
;>   val input_in_bounds_delay2 = fby(False, input_in_bounds_delay1)
;>   val last_in_bounds         = input_in_bounds && input_in_bounds_delay1 && input_in_bounds_delay2
;>
;>   val input_delay1           = fby(0, input)
;>   val input_delay2           = fby(0, input_delay1)
;>   val input_sum              = input + input_delay1 + input_delay2
;>   val mean                   = input_sum / 3
;>   val mean_in_bounds         = mean < MAXIMUM
;>
;>   last_in_bounds ==> mean_in_bounds
;> }
;
; The program is very similar. We now have four instances of the followed-by
; primitive instead of two. These new instances are delays of delays:
; `input_in_bounds_delay2` is a delayed version of `input_in_bounds_delay1`,
; which in turn is a delay of `input_in_bounds`.
;
; We reset the SMT solver to forget about the previous transition system, and
; convert the new property to a new transition system. The translation is very
; similar to the previous one.
(reset)
(declare-const MAXIMUM Int)

(declare-datatype State
  ((State
    (input_in_bounds_delay1 Bool)
    (input_in_bounds_delay2 Bool)
    (input_delay1           Int)
    (input_delay2           Int))))

(declare-datatype Row
  ((Row
    (input           Int)
    (input_in_bounds Bool)
    (last_in_bounds  Bool)
    (input_sum       Int)
    (mean            Int)
    (mean_in_bounds  Bool))))

(define-fun init ((state State)) Bool
  (and
    (= (input_in_bounds_delay1 state) false)
    (= (input_in_bounds_delay2 state) false)
    (= (input_delay1           state) 0)
    (= (input_delay2           state) 0)))

(define-fun step ((state State) (row Row) (stateX State)) Bool
  (and
    (= (input_in_bounds_delay1 stateX) (input_in_bounds        row))
    (= (input_in_bounds_delay2 stateX) (input_in_bounds_delay1 state))
    (= (input_delay1           stateX) (input                  row))
    (= (input_delay2           stateX) (input_delay1           state))))

(define-fun extract ((state State) (row Row)) Bool
  (and
    (= (input_in_bounds row) (< (input row) MAXIMUM))
    (= (last_in_bounds  row) (and (input_in_bounds row) (input_in_bounds_delay1 state) (input_in_bounds_delay2 state)))
    (= (input_sum       row) (+ (input row) (input_delay1 state) (input_delay2 state)))
    (= (mean            row) (/ (input_sum row) 3))
    (= (mean_in_bounds  row) (< (mean row) MAXIMUM))))

(define-fun prop ((row Row)) Bool
  (=> (last_in_bounds row) (mean_in_bounds row)))

(declare-const state0 State)
(declare-const row0   Row)

; Now we can try to inductively prove our new property. We start with the base
; case, as before, and show that we cannot violate the property from the
; initial state.
(push)
; Find values for state0, row0, such that...
; state0 describes an initial state; and
(assert (init    state0))
; the pure bindings have the right values; and
(assert (extract state0 row0))
; it violates the property.
(assert (not (prop row0)))

; The problem is unsatisfiable, as we hoped.
(echo "inductive base case. expect unsat")
(check-sat)
(pop)

; We then try to prove the inductive step case.
(declare-const state1 State)
(declare-const row1   Row)

(push)
; Find values for state0, row0, state1, row1, such that...
; the pure bindings in row0 correspond to state state0; and
(assert (extract state0 row0))
; the starting state state0 takes a step to successor state1; and
(assert (step    state0 row0 state1))
; the pure bindings in row1 correspond to the successor state; and
(assert (extract state1 row1))
; the property holds in the starting state's corresponding pure values; and
(assert (prop row0))
; the successor state's corresponding pure values violate the property.
(assert (not (prop row1)))

; Now we ask the solver. Unfortunately, the solver is able to find a satisfying
; solution that violates our property, which means that we couldn't prove our
; property.
(echo "inductive step case. expect sat")
(check-sat)
; We ask the SMT solver to give us the solution that it found. You can get the
; whole solution by calling (get-model) but to make it a bit easier to read
; we'll just extract the specific bits we're interested in, which is the
; starting state that led to the violation of the property.
(get-value (
  MAXIMUM
  (input_in_bounds_delay1 state0)
  (input_in_bounds_delay2 state0)
  (input_delay1           state0)
  (input_delay2           state0)
))

; On my machine, I get the following solution.
; 
;> ((MAXIMUM 1)
;>  ((input_in_bounds_delay1 state0) true)
;>  ((input_in_bounds_delay2 state0) false)
;>  ((input_delay1           state0) 23198)
;>  ((input_delay2           state0) (- 23198)))
;
; This solution is called a _counterexample-to-induction_ because it shows why
; the inductive proof failed. It's important to distinguish this from a true
; counterexample, which is a real execution trace that starts from an initial
; state and shows that the property is definitely false. A counterexample-to-
; -induction, on the other hand, doesn't necessarily tell us whether the
; property is true or false. The property may in fact be true, but it just
; isn't strong enough to be an inductive hypothesis on its own.
;
; In this case, when we inspect the solution, we see something odd: the state
; for `input_in_bounds_delay1` should contain the delayed value of 
; `input_in_bounds = input < MAXIMUM`, while the state for `input_delay1`
; should contain the delayed value of `input`. However, here we have a true
; value for the delayed bounds-check, while the delayed input value of 23198 is
; much larger than the maximum upper bound of one. This starting state doesn't
; make any sense, and there's no way for a real execution of the system to
; reach it. We need to strengthen our inductive hypothesis somehow so that this
; unreachable state is not considered by the inductive step.
;
; As a human looking at the problem, we could probably come up with an extra
; invariant that we could use to filter out this spurious counterexample-to-induction:
;
;> input_in_bounds_delay1 = input_delay1 < MAXIMUM
;
; However, since we intend to prove these properties inside a model checker, we
; don't want to put the burden of coming up with these new invariants on the
; end-user. We want some automatic way to synthesise the needed invariants.
; There are invariant generation techniques that look at such
; counterexamples-to-induction and try to generalise them, but they tend to be
; based on heuristics.
;
; Instead, we can use a technique called k-induction to avoid having to come
; up with these invariants ourselves. K-induction is a generalisation of regular
; induction that assumes the property holds for k previous steps and then tries
; to show that the property holds for the next step. When k = 1, k-induction
; corresponds to regular induction.
;
(pop)

; We will next try k-induction with k = 2. We declare a new state and row.
(declare-const state2 State)
(declare-const row2   Row)

(push)

; Now we state our problem. Find states state0, state1 and state2 such that...
(assert (extract state0 row0))
; state0 steps to state1; and
(assert (step    state0 row0 state1))
(assert (extract state1 row1))
; state1 steps to state2; and
(assert (step    state1 row1 state2))
(assert (extract state2 row2))
; the property holds at time 0; and
(assert (prop row0))
; the property holds at time 1; and
(assert (prop row1))
; the successor state at time 2 violates the property.
(assert (not (prop row2)))

; We ask the SMT solver to find a solution. It is unsatisfiable, which means
; that the k-inductive step case holds. The extra context about the two steps of
; history is enough to prove the property, and the user hasn't had to come up
; with any extra invariants.
(echo "k-inductive k=2 step case. expect unsat")
(check-sat)
; z3 says: unsat
(pop)

; The k-inductive base case is also a little different. In regular induction we
; just show that the initial state satisfies the property. For k-induction, we
; have to show that the first k steps satisfy the property.
(push)
; Find values for state0, state1, such that...
; state0 is an initial state; and
(assert (init state0))
(assert (extract state0 row0))
; state0 steps to state1; and
(assert (step    state0 row0 state1))
(assert (extract state1 row1))
; we reach a bad state in 1 or 2 steps.
(assert (or (not (prop row0)) (not (prop row1))))
(echo "k-inductive k=2 base case. expect unsat")
(check-sat)
; z3 says: unsat
(pop)

; ## Larger histories
;
; With that, we have successfuly proved the property we wanted. However, if we
; kept increasing the size of the history, we would probably need even more
; k-inductive steps. Increasing the number of k-inductive steps can be
; expensive because we require more state variables and more constraints.
; If we wanted to prove the same property with a large history, we might be
; better off re-writing our program to be easier to prove in the first place.
;
; The core issue is that we have a delayed version of `input` and a separate
; delayed version of `input < MAXIMUM`. The encoding to a transition system
; obscures the inherent connection that the different delayed values. We could
; try to recover this connection with heuristic transformations, but I don't
; know how reliable that will be.
;
; Another idea is to slightly change the way the program is written. If we
; rewrote the `LastN(HISTORY, input < MAXIMUM)` check to delay the input
; instead of the condition, then both sides of the implication would refer to
; the same delayed value. In an embedded language we can implement this with a
; higher-order function something like:
;
;> def MapLastN[T](n: Int, e: Stream[T])(f: T => Bool): Stream[Bool] = n match
;>   case 0 => True
;>   case 1 => f(e)
;>   case _ => f(e) && LastN(n - 1, fby(False, e))(f)
;
; which we would call with:
;
;> MapLastN(HISTORY, input)(_ < MAXIMUM) ==> MeanN(HISTORY, input) < MAXIMUM
;
; In cases like this, having a nice functional meta-language might help us to
; express our programs in ways that are more obviously correct.
;
; If we actually wanted to execute this code with a large history, however,
; this implementation has poor complexity. To sum a large history, we might
; want to keep the current version as the specification and implement it with
; a circular buffer and a running sum.
;

