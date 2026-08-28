import Silean.Contracts.Fifo.FifoCycleRefinement
import Silean.Contracts.Fifo.FifoPortContract
import Silean.Modules.OneEntryFifo.OneEntryFifo

namespace Silean.Modules.OneEntryFifo

open Silean

/-! Relates the one-entry FIFO's exact cycle contract to the abstract FIFO
contract using a logical queue of length zero or one. No hardware is defined
in this file. -/

private abbrev FifoPayload (element : SignalType) :=
  (Silean.Contracts.Fifo.standardContract element 1).Payload

private def logicalQueue (element : SignalType)
    (state : (cycleContract element).state.Values) : List (FifoPayload element) :=
  bif state .storedValid then [(state .storedData, ())] else []

def cycleRefinement (element : SignalType) :
    Contracts.Fifo.FifoCycleRefinement (certified element) (Silean.Contracts.Fifo.standardContract element 1) where
  Invariant := fun _ => True
  queue := logicalQueue element
  bounded := by
    intro state _
    change (cycleContract element).state.Values at state
    cases valid : state .storedValid <;>
      simp [logicalQueue, valid, Silean.Contracts.Fifo.standardContract]
  reset := by
    intro inputs state reset
    change (cycleContract element).state.Values at state
    change inputs .reset = true at reset
    constructor
    · trivial
    · change logicalQueue element
          ((stateRule element).apply inputs state) = []
      unfold logicalQueue
      rw [next_storedValid_of_reset element inputs state reset]
      rfl
  ordinary := by
    intro inputs state _ notReset
    change (cycleContract element).state.Values at state
    change inputs .reset = false at notReset
    constructor
    · trivial
    · generalize validEq : state .storedValid = valid
      generalize inputValidEq : inputs .inputValid = inputValid
      generalize outputReadyEq : inputs .outputReady = outputReady
      cases valid <;> cases inputValid <;> cases outputReady <;>
        simp [logicalQueue, Silean.Contracts.Fifo.standardContract, Silean.Interfaces.Fifo.sink, Silean.Interfaces.Fifo.source,
          Contracts.Fifo.FifoContract.inputTransfer, Contracts.Fifo.FifoContract.outputTransfer,
          Interfaces.ValidReadySample.transferredPayload?, Interfaces.ValidReadySample.transfers,
          Interfaces.ValidReadySink.sample, Interfaces.ValidReadySource.sample,
          validEq, inputValidEq, outputReadyEq, notReset,
          Silean.Interfaces.Fifo.inputMap, Silean.Interfaces.Fifo.outputMap, SignalType.Denote,
          SignalSelection.project, SignalMap.select]

noncomputable def fifoCertified (element : SignalType) :
    Contracts.Fifo.FifoCertified (Silean.Interfaces.Fifo.ports element) (Silean.Interfaces.Fifo.payloadTypes element) :=
  (cycleRefinement element).certify

@[simp] theorem fifoCertified_moduleStructure (element : SignalType) :
    (fifoCertified element).moduleStructure = moduleStructure element := rfl

@[simp] theorem fifoCertified_contract (element : SignalType) :
    (fifoCertified element).contract = Silean.Contracts.Fifo.standardContract element 1 := rfl

end Silean.Modules.OneEntryFifo
