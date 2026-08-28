import Silean.Modules.OneEntryFifoProperties

namespace Silean.Examples.Checks.OneEntryFifoProperties

open Silean.Contracts
open Silean.Modules

def payloadType : SignalType :=
  .tuple (.cons (.vector 3 .bit) (.cons .bit .nil))

def initial : OneEntryFifo.Properties.ContractState payloadType := fun
  | .storedValid => false
  | .storedData => payloadType.default

def input : OneEntryFifo.Properties.CycleInput payloadType where
  enqValid := true
  enqData := payloadType.default
  deqReady := false

example : Contracts.NoResetFifo.Contract 1 0
    (OneEntryFifo.Properties.trace payloadType initial [input]) :=
  OneEntryFifo.Properties.satisfies_contract payloadType initial [input]

example : Contracts.NoResetFifo.View.Satisfies
    (OneEntryFifo.Properties.fifoView payloadType)
    (OneEntryFifo.Properties.executes payloadType) :=
  OneEntryFifo.Properties.fifoView_satisfies payloadType

example
    (inputs : (NoResetFifo.ports payloadType).inputs.Values)
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

end Silean.Examples.Checks.OneEntryFifoProperties
