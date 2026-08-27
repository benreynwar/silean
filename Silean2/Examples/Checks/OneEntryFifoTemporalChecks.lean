import Silean2.Modules.OneEntryFifoTemporal

namespace Silean2.Examples.Checks.OneEntryFifoTemporal

open Silean2.Contracts
open Silean2.Modules

def payloadType : SignalType :=
  .tuple (.cons (.vector 3 .bit) (.cons .bit .nil))

def initial : OneEntryFifo.Temporal.ContractState payloadType := fun
  | .storedValid => false
  | .storedData => payloadType.default

def input : OneEntryFifo.Temporal.CycleInput payloadType where
  enqValid := true
  enqData := payloadType.default
  deqReady := false

example : Contracts.NoResetFifo.Contract 1 0
    (OneEntryFifo.Temporal.trace payloadType initial [input]) :=
  OneEntryFifo.Temporal.satisfies_contract payloadType initial [input]

example : Contracts.NoResetFifo.ModuleView.Satisfies
    (OneEntryFifo.Temporal.fifoView payloadType)
    (OneEntryFifo.Temporal.executes payloadType) :=
  OneEntryFifo.Temporal.fifoView_satisfies payloadType

example
    (inputs : (OneEntryFifo.ports payloadType).inputs.Values)
    (contractState :
      (OneEntryFifo.certified payloadType).cycleContract.state.Values)
    (structuralState :
      (OneEntryFifo.certified payloadType).moduleStructure.State)
    (proposal :
      ProposedValues (OneEntryFifo.certified payloadType).moduleStructure)
    (corresponds : (OneEntryFifo.certified payloadType).stateCorresponds
      contractState structuralState)
    (satisfies : (OneEntryFifo.certified payloadType).moduleStructure.IsSolution
      inputs structuralState proposal) :
    proposal.outputs =
        ((OneEntryFifo.certified payloadType).cycleContract.evaluate
          inputs contractState).1 ∧
      (OneEntryFifo.certified payloadType).stateCorresponds
        ((OneEntryFifo.certified payloadType).cycleContract.evaluate
          inputs contractState).2 proposal.nextState :=
  (OneEntryFifo.certified payloadType).solution_matches_evaluate
    inputs contractState structuralState proposal corresponds satisfies

end Silean2.Examples.Checks.OneEntryFifoTemporal
