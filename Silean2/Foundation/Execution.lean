namespace Silean2.Execution

/-! Generic finite traces for relational state transitions. -/

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

/-- The state and observation produced by one deterministic step. -/
structure StepResult (State Observation : Type) where
  nextState : State
  observation : Observation

/-- The final state and observations produced by a finite run. -/
structure RunResult (State Observation : Type) where
  finalState : State
  observations : List Observation

/-- A deterministic state machine. Contract-specific layers give `Input` and
    `Observation` their behavioral meaning. -/
structure Model (State Input Observation : Type) where
  step : State → Input → StepResult State Observation

namespace Model

def run (model : Model State Input Observation) : State → List Input →
    RunResult State Observation
  | state, [] => ⟨state, []⟩
  | state, input :: inputs =>
      let first := model.step state input
      let rest := model.run first.nextState inputs
      ⟨rest.finalState, first.observation :: rest.observations⟩

end Model

end Silean2.Execution
