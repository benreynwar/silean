import Silean.Modules.Fifo.FifoCertified
import Silean.Modules.OneEntryFifo.OneEntryFifoCertified
import Silean.Modules.SerialDepthFifo.SerialDepthFifoCertified

namespace Silean.Examples.Checks.FifoContract

open Silean
open Silean.Modules

example : (Silean.Contracts.Fifo.standardContract .bit 4).sink = Silean.Interfaces.Fifo.sink .bit := rfl
example : (Silean.Contracts.Fifo.standardContract .bit 4).source = Silean.Interfaces.Fifo.source .bit := rfl
example : (Silean.Contracts.Fifo.standardContract .bit 4).reset = .reset := rfl
example : (Silean.Contracts.Fifo.standardContract .bit 4).capacity = 4 := rfl

def resetInputs : (Silean.Interfaces.Fifo.ports .bit).inputs.Values
  | .inputValid | .inputData | .outputReady => false
  | .reset => true

def arbitraryOutputs : (Silean.Interfaces.Fifo.ports .bit).outputs.Values
  | .outputValid | .outputData | .inputReady => false

example : (Silean.Contracts.Fifo.standardContract .bit 1).Accepts [resetInputs] [arbitraryOutputs] := by
  refine ⟨(Silean.Contracts.Fifo.standardContract .bit 1).resetSynchronization, ?_⟩
  exact .cons resetInputs arbitraryOutputs (.reset rfl)
    (.nil (Silean.Contracts.Fifo.standardContract .bit 1).resetSynchronization)

noncomputable example : Contracts.Fifo.FifoCertified (Silean.Interfaces.Fifo.ports .bit) (Silean.Interfaces.Fifo.payloadTypes .bit) :=
  OneEntryFifo.fifoCertified .bit

noncomputable example : Contracts.Fifo.FifoCertified (Silean.Interfaces.Fifo.ports .bit) (Silean.Interfaces.Fifo.payloadTypes .bit) :=
  SerialDepthFifo.fifoCertified .bit 3 (by omega)

noncomputable example : Contracts.Fifo.FifoCertified (Silean.Interfaces.Fifo.ports .bit) (Silean.Interfaces.Fifo.payloadTypes .bit) :=
  Fifo.fifoCertified .bit 2

example (inputs : (Silean.Interfaces.Fifo.ports .bit).inputs.Values)
    (state : (OneEntryFifo.fifoCertified .bit).moduleStructure.State) :
    ∃ outputs nextState,
      (OneEntryFifo.fifoCertified .bit).moduleStructure.Transition
        inputs state outputs nextState :=
  (OneEntryFifo.fifoCertified .bit).transition_exists inputs state

example (state : (OneEntryFifo.fifoCertified .bit).moduleStructure.State)
    (inputs : List (Silean.Interfaces.Fifo.ports .bit).inputs.Values) :
    ∃ outputs finalState,
      (OneEntryFifo.fifoCertified .bit).moduleStructure.Executes
          state inputs outputs finalState ∧
        (OneEntryFifo.fifoCertified .bit).contract.Accepts inputs outputs :=
  (OneEntryFifo.fifoCertified .bit).accepted_execution_exists state inputs

example {contract : Contracts.Fifo.FifoContract ports payloadTypes}
    {initial final : contract.BoundedQueue}
    {inputs : List ports.inputs.Values} {outputs : List ports.outputs.Values}
    (trace : contract.OrdinaryTraceMatches initial inputs outputs final) :
    initial.1 ++ contract.transferredInputs inputs outputs =
      contract.transferredOutputs inputs outputs ++ final.1 :=
  Contracts.Fifo.FifoContract.OrdinaryTraceMatches.transfer_equation trace

example {contract : Contracts.Fifo.FifoContract ports payloadTypes}
    {final : contract.BoundedQueue}
    {inputs : List ports.inputs.Values} {outputs : List ports.outputs.Values}
    (trace : contract.OrdinaryTraceMatches contract.emptyQueue inputs outputs final) :
    (contract.transferredOutputs inputs outputs).IsPrefix
      (contract.transferredInputs inputs outputs) :=
  Contracts.Fifo.FifoContract.OrdinaryTraceMatches.outputs_prefix_inputs trace

example {contract : Contracts.Fifo.FifoContract ports payloadTypes}
    {inputs : List ports.inputs.Values} {outputs : List ports.outputs.Values}
    (trace : contract.OrdinaryTraceMatches contract.emptyQueue
      inputs outputs contract.emptyQueue) :
    contract.transferredInputs inputs outputs =
      contract.transferredOutputs inputs outputs :=
  Contracts.Fifo.FifoContract.OrdinaryTraceMatches.transfers_equal_when_drained trace

end Silean.Examples.Checks.FifoContract
