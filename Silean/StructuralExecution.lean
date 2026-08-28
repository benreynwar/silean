import Silean.StructuralDependency
import Silean.Foundation.Execution

namespace Silean

/-! Contract-independent execution of structural equations. A transition hides
the satisfying proposal while retaining its boundary outputs and derived next
state. -/

def ModuleStructure.Transition (module : ModuleStructure ports)
    (inputs : ports.inputs.Values) (currentState : module.State)
    (outputs : ports.outputs.Values) (nextState : module.State) : Prop :=
  ∃ proposal, module.IsSolution inputs currentState proposal ∧
    proposal.outputs = outputs ∧ proposal.nextState = nextState

abbrev ModuleStructure.Executes (module : ModuleStructure ports) :=
  Execution.Trace module.Transition

def ModuleStructure.HasSolution (module : ModuleStructure ports) : Prop :=
  ∀ inputs currentState,
    ∃ proposal, module.IsSolution inputs currentState proposal

def ModuleStructure.HasExactlyOneSolution
    (module : ModuleStructure ports) : Prop :=
  module.HasSolution ∧ module.HasAtMostOneSolution

namespace ModuleStructure

theorem transition_of_solution {module : ModuleStructure ports}
    {inputs : ports.inputs.Values} {currentState : module.State}
    {proposal : ProposedValues module}
    (solution : module.IsSolution inputs currentState proposal) :
    module.Transition inputs currentState proposal.outputs proposal.nextState :=
  ⟨proposal, solution, rfl, rfl⟩

theorem Transition.solution_exists
    {module : ModuleStructure ports} {inputs : ports.inputs.Values}
    {currentState : module.State} {outputs : ports.outputs.Values}
    {nextState : module.State}
    (transition : module.Transition inputs currentState outputs nextState) :
    ∃ proposal, module.IsSolution inputs currentState proposal := by
  rcases transition with ⟨proposal, solution, _, _⟩
  exact ⟨proposal, solution⟩

theorem Transition.unique
    {module : ModuleStructure ports} (unique : module.HasAtMostOneSolution)
    {inputs : ports.inputs.Values} {currentState : module.State}
    {leftOutputs rightOutputs : ports.outputs.Values}
    {leftNext rightNext : module.State}
    (left : module.Transition inputs currentState leftOutputs leftNext)
    (right : module.Transition inputs currentState rightOutputs rightNext) :
    leftOutputs = rightOutputs ∧ leftNext = rightNext := by
  rcases left with ⟨leftProposal, leftSolution, leftOutputsEq, leftNextEq⟩
  rcases right with ⟨rightProposal, rightSolution, rightOutputsEq, rightNextEq⟩
  have proposalsEqual := unique inputs currentState leftProposal rightProposal
    leftSolution rightSolution
  subst rightProposal
  exact ⟨leftOutputsEq.symm.trans rightOutputsEq,
    leftNextEq.symm.trans rightNextEq⟩

theorem Executes.length_eq
    {module : ModuleStructure ports} {initialState finalState : module.State}
    {inputs : List ports.inputs.Values} {outputs : List ports.outputs.Values}
    (execution : module.Executes initialState inputs outputs finalState) :
    outputs.length = inputs.length :=
  Execution.Trace.length_eq execution

theorem Executes.nil_iff
    {module : ModuleStructure ports} {initialState finalState : module.State} :
    module.Executes initialState [] [] finalState ↔ finalState = initialState :=
  Execution.Trace.nil_iff

theorem Executes.cons_iff
    {module : ModuleStructure ports} {initialState finalState : module.State}
    {input : ports.inputs.Values} {inputs : List ports.inputs.Values}
    {output : ports.outputs.Values} {outputs : List ports.outputs.Values} :
    module.Executes initialState (input :: inputs) (output :: outputs) finalState ↔
      ∃ nextState,
        module.Transition input initialState output nextState ∧
        module.Executes nextState inputs outputs finalState :=
  Execution.Trace.cons_iff

theorem Executes.single_iff
    {module : ModuleStructure ports} {initialState finalState : module.State}
    {input : ports.inputs.Values} {output : ports.outputs.Values} :
    module.Executes initialState [input] [output] finalState ↔
      module.Transition input initialState output finalState :=
  Execution.Trace.single_iff

theorem Executes.append
    {module : ModuleStructure ports}
    {initialState middleState finalState : module.State}
    {leftInputs rightInputs : List ports.inputs.Values}
    {leftOutputs rightOutputs : List ports.outputs.Values}
    (left : module.Executes initialState leftInputs leftOutputs middleState)
    (right : module.Executes middleState rightInputs rightOutputs finalState) :
    module.Executes initialState (leftInputs ++ rightInputs)
      (leftOutputs ++ rightOutputs) finalState :=
  Execution.Trace.append left right

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
  Execution.Trace.split execution lengths

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
  Execution.Trace.append_iff lengths

theorem HasSolution.transition_exists
    {module : ModuleStructure ports} (available : module.HasSolution)
    (inputs : ports.inputs.Values) (currentState : module.State) :
    ∃ outputs nextState,
      module.Transition inputs currentState outputs nextState := by
  rcases available inputs currentState with ⟨proposal, solution⟩
  exact ⟨proposal.outputs, proposal.nextState,
    transition_of_solution solution⟩

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
