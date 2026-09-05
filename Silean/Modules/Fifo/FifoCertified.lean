import Silean.Contracts.Fifo.FifoCycleRefinement
import Silean.Contracts.Fifo.FifoPortContract
import Silean.Modules.Fifo.FifoCycleCertified
import Silean.Modules.Fifo.FifoProperties

namespace Silean.Modules.Fifo

open Silean Silean.Interfaces.Fifo

/-! Proves that the pointer-and-register-bank FIFO implements the abstract FIFO
contract by relating its cycle state to a logical queue. This file contains no
additional hardware structure. -/

private def wrapPayload (value : element.Denote) :
    (payloadTypes element).Denote :=
  (value, ())

private def logicalQueue (element : SignalType) (addressWidth : Nat)
    (state : (cycleContract element addressWidth).state.Values) :
    List (Contracts.Fifo.standardContract element (Properties.capacity addressWidth)).Payload :=
  (Properties.contents addressWidth state).map wrapPayload

private def fifoRefinement (element : SignalType)
    (addressWidth : Nat) :
    Contracts.Fifo.FifoCycleRefinement (certified element addressWidth)
      (Contracts.Fifo.standardContract element (Properties.capacity addressWidth)) where
  Invariant := Properties.Invariant addressWidth
  queue := logicalQueue element addressWidth
  bounded := by
    intro state valid
    simpa [logicalQueue, Contracts.Fifo.standardContract] using
      Properties.contents_bounded addressWidth state valid
  reset := by
    intro inputs state reset
    change (stateMap element addressWidth).Values at state
    change inputs .reset = true at reset
    constructor
    · change Properties.Invariant addressWidth
        ((cycleContract element addressWidth).evaluate inputs state).2
      unfold Properties.Invariant Properties.occupancy
      rw [Properties.Evaluation.evaluated_next_readPointer,
        Properties.Evaluation.evaluated_next_writePointer]
      simp [reset, nextReadPointer, nextWritePointer,
        EnabledResetCounter.nextValue, Properties.pointerValue,
        Properties.capacity, BitVector.cardinality_eq_pow,
        CircularBuffer.distance]
    · unfold logicalQueue
      apply List.eq_nil_of_length_eq_zero
      simp only [List.length_map]
      change (Properties.contents addressWidth
        ((cycleContract element addressWidth).evaluate inputs state).2).length = 0
      rw [Properties.contents_length]
      unfold Properties.occupancy
      rw [Properties.Evaluation.evaluated_next_readPointer,
        Properties.Evaluation.evaluated_next_writePointer]
      simp [reset, nextReadPointer, nextWritePointer,
        EnabledResetCounter.nextValue, Properties.pointerValue,
        CircularBuffer.distance]
  ordinary := by
    intro inputs state valid notReset
    dsimp only
    simp only [certified_cycleContract]
    change (stateMap element addressWidth).Values at state
    change inputs .reset = false at notReset
    have nextValid := Properties.Evaluation.next_preserves_invariant element
      addressWidth state inputs valid
    have outputsEq := Properties.Evaluation.evaluated_outputs element addressWidth
      state inputs
    have ordinary := Properties.contentsOf_next_of_notReset addressWidth
      (state .entries) (state .readPointer) (state .writePointer)
      (inputs .outputReady) (inputs .inputValid) (inputs .inputData) valid
    constructor
    · exact nextValid
    ·
      rcases outputsEq with ⟨outputValidEq, outputDataEq, inputReadyEq⟩
      change ((cycleContract element addressWidth).evaluate inputs state).1 .outputValid = _
        at outputValidEq
      change ((cycleContract element addressWidth).evaluate inputs state).1 .outputData = _
        at outputDataEq
      change ((cycleContract element addressWidth).evaluate inputs state).1 .inputReady = _
        at inputReadyEq
      have mapped := congrArg (List.map wrapPayload) ordinary
      rw [Contracts.Fifo.standardContract_inputTransfer,
        Contracts.Fifo.standardContract_outputTransfer,
        inputReadyEq, outputValidEq, outputDataEq]
      unfold logicalQueue Properties.contents
      rw [
        Properties.Evaluation.evaluated_next_readPointer,
        Properties.Evaluation.evaluated_next_writePointer,
        Properties.Evaluation.evaluated_next_entries]
      rw [notReset]
      let oldQueue := List.map wrapPayload
        (Properties.contentsOf addressWidth (state .entries)
          (state .readPointer) (state .writePointer))
      let nextQueue := List.map wrapPayload
        (Properties.contentsOf addressWidth
          (nextEntries addressWidth (inputs .inputValid) (inputs .inputData)
            (state .readPointer) (state .writePointer) (state .entries))
          (nextReadPointer addressWidth false (inputs .outputReady)
            (state .readPointer) (state .writePointer))
          (nextWritePointer addressWidth false (inputs .inputValid)
            (state .readPointer) (state .writePointer)))
      let inputPayload : (payloadTypes element).Denote := (inputs .inputData, ())
      let outputPayload : (payloadTypes element).Denote :=
        (outputData addressWidth (state .readPointer) (state .entries), ())
      change oldQueue ++
          (bif inputs .inputValid &&
            Fifo.PointerControl.inputReady (state .readPointer) (state .writePointer)
            then [inputPayload] else []) =
        (bif Fifo.PointerControl.outputValid (state .readPointer) (state .writePointer) &&
            inputs .outputReady then [outputPayload] else []) ++ nextQueue
      cases inputAccepted : inputs .inputValid &&
          Fifo.PointerControl.inputReady (state .readPointer) (state .writePointer) <;>
        cases outputAccepted :
          Fifo.PointerControl.outputValid (state .readPointer) (state .writePointer) &&
            inputs .outputReady
      all_goals
        simp [inputAccepted, outputAccepted, Fifo.writeAdvance,
          Fifo.readAdvance,
          Fifo.PointerControl.writeAdvance, Fifo.PointerControl.readAdvance,
          oldQueue, nextQueue, inputPayload, outputPayload,
          List.map_append, wrapPayload] at mapped ⊢
        exact mapped

noncomputable def fifoCertified (element : SignalType)
    (addressWidth : Nat) :
    Contracts.Fifo.FifoCertified (ports element) (payloadTypes element) :=
  (fifoRefinement element addressWidth).certify

@[simp] theorem fifoCertified_moduleStructure (element : SignalType)
    (addressWidth : Nat) :
    (fifoCertified element addressWidth).moduleStructure =
      moduleStructure element addressWidth := rfl

@[simp] theorem fifoCertified_contract (element : SignalType)
    (addressWidth : Nat) :
    (fifoCertified element addressWidth).contract =
      Contracts.Fifo.standardContract element (Properties.capacity addressWidth) := rfl

end Silean.Modules.Fifo
