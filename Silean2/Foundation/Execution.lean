namespace Silean2.Execution

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
