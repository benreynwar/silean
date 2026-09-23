import Silean.Contracts.Cycle.CycleImplementation
import Silean.Semantics.StructuralExecution

namespace Silean.Contracts.Cycle

open Silean

/-! # Traces of cycle contracts

These definitions turn a one-cycle contract into a finite relational trace.
They are useful whenever a contract is assumed at an opaque boundary: the
contract state remains private to the proposition and is not exposed as part
of the module's structural interface.
-/

namespace ModuleCycleContract

/-- The four-argument transition relation induced by an allowed contract
step. -/
def Transition (contract : ModuleCycleContract ports)
    (inputs : ports.inputs.Values) (currentState : contract.state.Values)
    (outputs : ports.outputs.Values) (nextState : contract.state.Values) : Prop :=
  contract.Allows
    { inputs := inputs
      currentState := currentState
      outputs := outputs
      nextState := nextState }

/-- A finite input/output trace with properly threaded contract state. -/
abbrev TraceMatches (contract : ModuleCycleContract ports) :=
  Trace contract.Transition

/-- The boundary sequences are admitted from a specified initial contract
state. The final contract state remains hidden. -/
def AcceptsFrom (contract : ModuleCycleContract ports)
    (initialState : contract.state.Values)
    (inputs : List ports.inputs.Values)
    (outputs : List ports.outputs.Values) : Prop :=
  ∃ finalState, contract.TraceMatches initialState inputs outputs finalState

/-- The boundary sequences are admitted from some hidden initial contract
state. Contracts that constrain initialization should use `AcceptsFrom` or a
more specific wrapper instead. -/
def Accepts (contract : ModuleCycleContract ports)
    (inputs : List ports.inputs.Values)
    (outputs : List ports.outputs.Values) : Prop :=
  ∃ initialState, contract.AcceptsFrom initialState inputs outputs

/-- State-free form over an already paired boundary trace. -/
def AcceptsBoundaryTraceFrom (contract : ModuleCycleContract ports)
    (initialState : contract.state.Values)
    (trace : BoundaryTrace ports) : Prop :=
  contract.AcceptsFrom initialState trace.inputs trace.outputs

/-- State-free form over an already paired boundary trace, with both contract
endpoint states hidden. -/
def AcceptsBoundaryTrace (contract : ModuleCycleContract ports)
    (trace : BoundaryTrace ports) : Prop :=
  contract.Accepts trace.inputs trace.outputs

end ModuleCycleContract

namespace ModuleCycleCertification

/-- A concrete cycle certification discharges the corresponding trace
assumption for any one of its structural executions, starting from related
contract and structural states. -/
theorem traceMatches_of_executes
    {moduleStructure : ModuleStructure ports}
    {contract : ModuleCycleContract ports}
    (certification : ModuleCycleCertification moduleStructure contract)
    {structuralInitial structuralFinal : moduleStructure.State}
    {inputs : List ports.inputs.Values}
    {outputs : List ports.outputs.Values}
    (contractInitial : contract.state.Values)
    (corresponds : certification.stateCorresponds contractInitial
      structuralInitial)
    (execution : moduleStructure.Executes structuralInitial inputs outputs
      structuralFinal) :
    ∃ contractFinal,
      contract.TraceMatches contractInitial inputs outputs contractFinal ∧
      certification.stateCorresponds contractFinal structuralFinal := by
  induction execution generalizing contractInitial with
  | nil =>
      exact ⟨contractInitial, .nil contractInitial, corresponds⟩
  | @cons structuralCurrent structuralNext structuralFinal remainingInputs
      remainingOutputs input output transition rest induction =>
      rcases certification.implements contractInitial
          { inputs := input
            currentState := structuralCurrent
            outputs := output
            nextState := structuralNext }
          corresponds transition with
        ⟨contractNext, allowed, nextCorresponds⟩
      rcases induction contractNext nextCorresponds with
        ⟨contractFinal, remainingMatches, finalCorresponds⟩
      exact ⟨contractFinal,
        .cons input output allowed remainingMatches, finalCorresponds⟩

/-- A concrete cycle certification also discharges the state-hidden form of
the trace assumption. -/
theorem accepts_of_executes
    {moduleStructure : ModuleStructure ports}
    {contract : ModuleCycleContract ports}
    (certification : ModuleCycleCertification moduleStructure contract)
    {structuralInitial structuralFinal : moduleStructure.State}
    {inputs : List ports.inputs.Values}
    {outputs : List ports.outputs.Values}
    (execution : moduleStructure.Executes structuralInitial inputs outputs
      structuralFinal) :
    contract.Accepts inputs outputs := by
  rcases certification.hasCorrespondingState structuralInitial with
    ⟨contractInitial, corresponds⟩
  rcases certification.traceMatches_of_executes contractInitial corresponds
      execution with
    ⟨contractFinal, traceMatches, _⟩
  exact ⟨contractInitial, contractFinal, traceMatches⟩

/-- A related, caller-selected initial contract state discharges the
corresponding initial-state-specific boundary assumption. -/
theorem acceptsBoundaryTraceFrom_of_executes
    {moduleStructure : ModuleStructure ports}
    {contract : ModuleCycleContract ports}
    (certification : ModuleCycleCertification moduleStructure contract)
    {structuralInitial structuralFinal : moduleStructure.State}
    {inputs : List ports.inputs.Values}
    {outputs : List ports.outputs.Values}
    (contractInitial : contract.state.Values)
    (corresponds : certification.stateCorresponds contractInitial
      structuralInitial)
    (execution : moduleStructure.Executes structuralInitial inputs outputs
      structuralFinal) :
    contract.AcceptsBoundaryTraceFrom contractInitial
      execution.toBoundaryTrace := by
  unfold ModuleCycleContract.AcceptsBoundaryTraceFrom
  unfold ModuleCycleContract.AcceptsFrom
  rw [execution.toBoundaryTrace_inputs, execution.toBoundaryTrace_outputs]
  rcases certification.traceMatches_of_executes contractInitial corresponds
      execution with
    ⟨contractFinal, traceMatches, _⟩
  exact ⟨contractFinal, traceMatches⟩

/-- Boundary-trace form of `accepts_of_executes`. -/
theorem acceptsBoundaryTrace_of_executes
    {moduleStructure : ModuleStructure ports}
    {contract : ModuleCycleContract ports}
    (certification : ModuleCycleCertification moduleStructure contract)
    {structuralInitial structuralFinal : moduleStructure.State}
    {inputs : List ports.inputs.Values}
    {outputs : List ports.outputs.Values}
    (execution : moduleStructure.Executes structuralInitial inputs outputs
      structuralFinal) :
    contract.AcceptsBoundaryTrace execution.toBoundaryTrace := by
  unfold ModuleCycleContract.AcceptsBoundaryTrace
  simpa using certification.accepts_of_executes execution

end ModuleCycleCertification

end Silean.Contracts.Cycle
