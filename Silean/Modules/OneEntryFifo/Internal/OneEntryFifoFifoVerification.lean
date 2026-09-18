import Silean.Contracts.Fifo.FifoCycleRefinement
import Silean.Contracts.Fifo.FifoPortContract
import Silean.Modules.OneEntryFifo.OneEntryFifoCycleTheorems

/-! # One-entry FIFO refinement verification

This internal proof relates the exact cycle behavior of the one-entry FIFO to
the latency-independent FIFO contract. Downstream code should use the
certification exported by `OneEntryFifoFifoTheorems` rather than this witness.
-/

namespace Silean.Modules.OneEntryFifo.Internal

open Silean

private abbrev FifoPayload (element : SignalType) :=
  (Silean.Contracts.Fifo.standardContract element 1).Payload

private def logicalQueue (element : SignalType)
    (state : (cycleContract element).state.Values) : List (FifoPayload element) :=
  bif state .storedValid then [(state .storedData, ())] else []

def cycleRefinement (element : SignalType) :
    Contracts.Fifo.FifoCycleRefinement (certified element)
      (Silean.Contracts.Fifo.standardContract element 1) where
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
      simp [stateRule_apply_storedValid, reset]
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
        simp [logicalQueue, cycleContract, cycleBehavior,
          Silean.Contracts.Fifo.standardContract, Silean.Interfaces.Fifo.sink,
          Silean.Interfaces.Fifo.source,
          Contracts.Fifo.FifoContract.inputTransfer,
          Contracts.Fifo.FifoContract.outputTransfer,
          Interfaces.ValidReadySample.transferredPayload?,
          Interfaces.ValidReadySample.transfers,
          Interfaces.ValidReadySink.sample, Interfaces.ValidReadySource.sample,
          validEq, inputValidEq, outputReadyEq, notReset,
          Silean.Interfaces.Fifo.inputMap, Silean.Interfaces.Fifo.outputMap,
          SignalType.Denote, SignalSelection.project, SignalMap.select]

end Silean.Modules.OneEntryFifo.Internal
