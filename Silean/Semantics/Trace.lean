namespace Silean

/-! # Finite execution traces

This file lifts a one-step relational semantics into a finite execution. Given
a relation

```lean
Step : Input → State → Observation → State → Prop
```

`Trace Step` records a list of consecutive steps, threading the state produced
by one step into the next. Each input has one corresponding observation; for a
hardware module, that observation is the module's output values for the cycle.

The definition is intentionally independent of structural hardware semantics.
It is shared by `ModuleStructure.Executes` and by multi-cycle contracts such as
FIFO and reset behavior. The accompanying lemmas provide the common operations
needed by those users: decomposing, appending, and splitting traces.
-/

inductive Trace (Step : Input → State → Observation → State → Prop) :
    State → List Input → List Observation → State → Prop
  | nil (state) : Trace Step state [] [] state
  | cons {currentState nextState finalState inputs observations}
      (input : Input) (observation : Observation) :
      Step input currentState observation nextState →
      Trace Step nextState inputs observations finalState →
      Trace Step currentState (input :: inputs)
        (observation :: observations) finalState

namespace Trace

theorem length_eq
    {Step : Input → State → Observation → State → Prop}
    {initialState finalState : State} {inputs : List Input}
    {observations : List Observation}
    (trace : Trace Step initialState inputs observations finalState) :
    observations.length = inputs.length := by
  induction trace with
  | nil => rfl
  | cons _ _ _ _ induction => simp [induction]

theorem nil_iff
    {Step : Input → State → Observation → State → Prop}
    {initialState finalState : State} :
    Trace Step initialState [] [] finalState ↔ finalState = initialState := by
  constructor
  · intro trace
    cases trace
    rfl
  · intro equal
    cases equal
    exact .nil initialState

theorem cons_iff
    {Step : Input → State → Observation → State → Prop}
    {initialState finalState : State} {input : Input} {inputs : List Input}
    {observation : Observation} {observations : List Observation} :
    Trace Step initialState (input :: inputs) (observation :: observations)
        finalState ↔
      ∃ nextState,
        Step input initialState observation nextState ∧
        Trace Step nextState inputs observations finalState := by
  constructor
  · intro trace
    cases trace with
    | cons _ _ step rest => exact ⟨_, step, rest⟩
  · rintro ⟨nextState, step, rest⟩
    exact .cons input observation step rest

theorem single_iff
    {Step : Input → State → Observation → State → Prop}
    {initialState finalState : State} {input : Input}
    {observation : Observation} :
    Trace Step initialState [input] [observation] finalState ↔
      Step input initialState observation finalState := by
  constructor
  · intro trace
    cases trace with
    | cons _ _ step rest =>
        cases rest
        exact step
  · intro step
    exact .cons input observation step (.nil finalState)

theorem append
    {Step : Input → State → Observation → State → Prop}
    {initialState middleState finalState : State}
    {leftInputs rightInputs : List Input}
    {leftObservations rightObservations : List Observation}
    (left : Trace Step initialState leftInputs leftObservations middleState)
    (right : Trace Step middleState rightInputs rightObservations finalState) :
    Trace Step initialState (leftInputs ++ rightInputs)
      (leftObservations ++ rightObservations) finalState := by
  induction left with
  | nil => exact right
  | cons input observation step _ induction =>
      exact .cons input observation step (induction right)

theorem split
    {Step : Input → State → Observation → State → Prop}
    {initialState finalState : State}
    {leftInputs rightInputs : List Input}
    {leftObservations rightObservations : List Observation}
    (trace : Trace Step initialState (leftInputs ++ rightInputs)
      (leftObservations ++ rightObservations) finalState)
    (lengths : leftObservations.length = leftInputs.length) :
    ∃ middleState,
      Trace Step initialState leftInputs leftObservations middleState ∧
      Trace Step middleState rightInputs rightObservations finalState := by
  induction leftInputs generalizing initialState leftObservations with
  | nil =>
      have observationsNil : leftObservations = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using lengths)
      subst leftObservations
      exact ⟨initialState, .nil initialState, trace⟩
  | cons input inputs induction =>
      cases leftObservations with
      | nil => simp at lengths
      | cons observation observations =>
          cases trace with
          | cons _ _ step rest =>
              have tailLengths : observations.length = inputs.length := by
                simpa using lengths
              rcases induction rest tailLengths with
                ⟨middleState, left, right⟩
              exact ⟨middleState, .cons input observation step left, right⟩

theorem append_iff
    {Step : Input → State → Observation → State → Prop}
    {initialState finalState : State}
    {leftInputs rightInputs : List Input}
    {leftObservations rightObservations : List Observation}
    (lengths : leftObservations.length = leftInputs.length) :
    Trace Step initialState (leftInputs ++ rightInputs)
        (leftObservations ++ rightObservations) finalState ↔
      ∃ middleState,
        Trace Step initialState leftInputs leftObservations middleState ∧
        Trace Step middleState rightInputs rightObservations finalState := by
  constructor
  · exact fun trace => trace.split lengths
  · rintro ⟨middleState, left, right⟩
    exact left.append right

end Trace

end Silean
