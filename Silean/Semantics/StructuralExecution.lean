import Silean.Semantics.StructuralDependency
import Silean.Semantics.Trace

namespace Silean

/-! # Execution derived from structural equations

A structural transition exists when there is a complete hierarchy assignment
satisfying all simultaneous equations. The transition hides that internal
assignment and keeps only boundary outputs and next structural state.
`Executes` repeats this relation over an input trace.

This does not introduce a solver or evaluation order. `HasSolution` establishes
that transitions exist; `HasAtMostOneSolution` establishes determinism. When
both hold, the structure has exactly one output and next state for every input
and current state. -/

def ModuleStructure.Transition (module : ModuleStructure ports)
    (inputs : ports.inputs.Values) (currentState : module.State)
    (outputs : ports.outputs.Values) (nextState : module.State) : Prop :=
  module.Realizes
    { inputs := inputs
      currentState := currentState
      outputs := outputs
      nextState := nextState }

abbrev ModuleStructure.Executes (module : ModuleStructure ports) :=
  Trace module.Transition

namespace ModuleStructure

/-- The four-argument transition is exactly the structural relation on
the corresponding boundary step. -/
theorem transition_iff_realizes {module : ModuleStructure ports}
    {inputs : ports.inputs.Values} {currentState : module.State}
    {outputs : ports.outputs.Values} {nextState : module.State} :
    module.Transition inputs currentState outputs nextState ↔
      module.Realizes
        { inputs := inputs
          currentState := currentState
          outputs := outputs
          nextState := nextState } :=
  Iff.rfl

theorem transition_of_solution {module : ModuleStructure ports}
    {hierStep : HierStep module} (solution : module.IsSolution hierStep) :
    module.Transition hierStep.inputs (HierStep.currentState module hierStep)
      hierStep.outputs (HierStep.nextState module hierStep) :=
  realizes_of_solution solution

theorem Transition.solution_exists
    {module : ModuleStructure ports} {inputs : ports.inputs.Values}
    {currentState : module.State} {outputs : ports.outputs.Values}
    {nextState : module.State}
    (transition : module.Transition inputs currentState outputs nextState) :
    ∃ hierStep, module.IsSolution hierStep ∧
      hierStep.step =
        { inputs := inputs
          currentState := currentState
          outputs := outputs
          nextState := nextState } :=
  transition

theorem Transition.unique
    {module : ModuleStructure ports} (unique : module.HasAtMostOneSolution)
    {inputs : ports.inputs.Values} {currentState : module.State}
    {leftOutputs rightOutputs : ports.outputs.Values}
    {leftNext rightNext : module.State}
    (left : module.Transition inputs currentState leftOutputs leftNext)
    (right : module.Transition inputs currentState rightOutputs rightNext) :
    leftOutputs = rightOutputs ∧ leftNext = rightNext := by
  rcases left with ⟨leftHierStep, leftSolution, leftStepEq⟩
  rcases right with ⟨rightHierStep, rightSolution, rightStepEq⟩
  have inputsEqual : leftHierStep.inputs = rightHierStep.inputs := by
    change leftHierStep.step.inputs = rightHierStep.step.inputs
    rw [leftStepEq, rightStepEq]
  have currentStatesEqual :
      HierStep.currentState module leftHierStep =
        HierStep.currentState module rightHierStep := by
    change leftHierStep.step.currentState = rightHierStep.step.currentState
    rw [leftStepEq, rightStepEq]
  have hierarchyEqual := unique leftHierStep rightHierStep
    leftSolution rightSolution inputsEqual currentStatesEqual
  subst rightHierStep
  have boundaryEqual := leftStepEq.symm.trans rightStepEq
  exact ⟨congrArg CycleStep.outputs boundaryEqual,
    congrArg CycleStep.nextState boundaryEqual⟩

theorem Executes.length_eq
    {module : ModuleStructure ports} {initialState finalState : module.State}
    {inputs : List ports.inputs.Values} {outputs : List ports.outputs.Values}
    (execution : module.Executes initialState inputs outputs finalState) :
    outputs.length = inputs.length :=
  Trace.length_eq execution

theorem Executes.nil_iff
    {module : ModuleStructure ports} {initialState finalState : module.State} :
    module.Executes initialState [] [] finalState ↔ finalState = initialState :=
  Trace.nil_iff

theorem Executes.cons_iff
    {module : ModuleStructure ports} {initialState finalState : module.State}
    {input : ports.inputs.Values} {inputs : List ports.inputs.Values}
    {output : ports.outputs.Values} {outputs : List ports.outputs.Values} :
    module.Executes initialState (input :: inputs) (output :: outputs) finalState ↔
      ∃ nextState,
        module.Transition input initialState output nextState ∧
        module.Executes nextState inputs outputs finalState :=
  Trace.cons_iff

theorem Executes.single_iff
    {module : ModuleStructure ports} {initialState finalState : module.State}
    {input : ports.inputs.Values} {output : ports.outputs.Values} :
    module.Executes initialState [input] [output] finalState ↔
      module.Transition input initialState output finalState :=
  Trace.single_iff

theorem Executes.append
    {module : ModuleStructure ports}
    {initialState middleState finalState : module.State}
    {leftInputs rightInputs : List ports.inputs.Values}
    {leftOutputs rightOutputs : List ports.outputs.Values}
    (left : module.Executes initialState leftInputs leftOutputs middleState)
    (right : module.Executes middleState rightInputs rightOutputs finalState) :
    module.Executes initialState (leftInputs ++ rightInputs)
      (leftOutputs ++ rightOutputs) finalState :=
  Trace.append left right

theorem Executes.split
    {module : ModuleStructure ports}
    {initialState finalState : module.State}
    {leftInputs rightInputs : List ports.inputs.Values}
    {leftOutputs rightOutputs : List ports.outputs.Values}
    (execution : module.Executes initialState (leftInputs ++ rightInputs)
      (leftOutputs ++ rightOutputs) finalState)
    (lengths : leftOutputs.length = leftInputs.length) :
    ∃ middleState,
      module.Executes initialState leftInputs leftOutputs middleState ∧
      module.Executes middleState rightInputs rightOutputs finalState :=
  Trace.split execution lengths

theorem executes_append_iff
    {module : ModuleStructure ports}
    {initialState finalState : module.State}
    {leftInputs rightInputs : List ports.inputs.Values}
    {leftOutputs rightOutputs : List ports.outputs.Values}
    (lengths : leftOutputs.length = leftInputs.length) :
    module.Executes initialState (leftInputs ++ rightInputs)
        (leftOutputs ++ rightOutputs) finalState ↔
      ∃ middleState,
        module.Executes initialState leftInputs leftOutputs middleState ∧
        module.Executes middleState rightInputs rightOutputs finalState :=
  Trace.append_iff lengths

theorem HasSolution.transition_exists
    {module : ModuleStructure ports} (available : module.HasSolution)
    (inputs : ports.inputs.Values) (currentState : module.State) :
    ∃ outputs nextState,
      module.Transition inputs currentState outputs nextState := by
  rcases available inputs currentState with
    ⟨hierStep, solution, inputsEqual, currentStateEqual⟩
  refine ⟨hierStep.outputs, HierStep.nextState module hierStep, ?_⟩
  rw [← inputsEqual, ← currentStateEqual]
  exact transition_of_solution solution

theorem HasSolution.execution_exists
    {module : ModuleStructure ports} (available : module.HasSolution) :
    ∀ (initialState : module.State) (inputs : List ports.inputs.Values),
      ∃ outputs finalState, module.Executes initialState inputs outputs finalState
  | initialState, [] => ⟨[], initialState, .nil initialState⟩
  | initialState, input :: inputs => by
      rcases available.transition_exists input initialState with
        ⟨output, nextState, transition⟩
      rcases available.execution_exists nextState inputs with
        ⟨outputs, finalState, rest⟩
      exact ⟨output :: outputs, finalState,
        .cons input output transition rest⟩

theorem HasExactlyOneSolution.transition_exists_unique
    {module : ModuleStructure ports} (exact : module.HasExactlyOneSolution)
    (inputs : ports.inputs.Values) (currentState : module.State) :
    ∃ outputs nextState,
      module.Transition inputs currentState outputs nextState ∧
      ∀ otherOutputs otherNext,
        module.Transition inputs currentState otherOutputs otherNext →
        otherOutputs = outputs ∧ otherNext = nextState := by
  rcases exact.1.transition_exists inputs currentState with
    ⟨outputs, nextState, transition⟩
  exact ⟨outputs, nextState, transition, fun otherOutputs otherNext other =>
    other.unique exact.2 transition⟩

theorem Executes.unique
    {module : ModuleStructure ports} (unique : module.HasAtMostOneSolution)
    {initialState : module.State} {inputs : List ports.inputs.Values}
    {leftOutputs rightOutputs : List ports.outputs.Values}
    {leftFinal rightFinal : module.State}
    (left : module.Executes initialState inputs leftOutputs leftFinal)
    (right : module.Executes initialState inputs rightOutputs rightFinal) :
    leftOutputs = rightOutputs ∧ leftFinal = rightFinal := by
  induction left generalizing rightOutputs rightFinal with
  | nil =>
      cases right
      exact ⟨rfl, rfl⟩
  | cons input output transition rest induction =>
      cases right with
      | cons _ rightOutput rightTransition rightRest =>
          rcases transition.unique unique rightTransition with
            ⟨outputsEqual, statesEqual⟩
          subst rightOutput
          cases statesEqual
          rcases induction rightRest with ⟨tailsEqual, finalsEqual⟩
          exact ⟨congrArg (List.cons output) tailsEqual, finalsEqual⟩

theorem HasExactlyOneSolution.execution_exists_unique
    {module : ModuleStructure ports} (exact : module.HasExactlyOneSolution)
    (initialState : module.State) (inputs : List ports.inputs.Values) :
    ∃ outputs finalState,
      module.Executes initialState inputs outputs finalState ∧
      ∀ otherOutputs otherFinal,
        module.Executes initialState inputs otherOutputs otherFinal →
        otherOutputs = outputs ∧ otherFinal = finalState := by
  rcases exact.1.execution_exists initialState inputs with
    ⟨outputs, finalState, execution⟩
  exact ⟨outputs, finalState, execution, fun otherOutputs otherFinal other =>
    other.unique exact.2 execution⟩

end ModuleStructure

end Silean
