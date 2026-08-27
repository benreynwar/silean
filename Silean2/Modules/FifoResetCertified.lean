import Silean2.Modules.FifoResetContract
import Silean2.ModuleResetCertified
import Silean2.Modules.FifoProperties

namespace Silean2.Modules.Fifo

open Silean2

private abbrev CycleState (element : SignalType) (addressWidth : Nat) :=
  (certified element addressWidth).cycleContract.state.Values

private def Aligned (element : SignalType) (addressWidth : Nat)
    (cycleState : CycleState element addressWidth) :
    (resetContract element addressWidth).Synchronization → Prop
  | none => True
  | some queue =>
      Properties.Invariant addressWidth cycleState ∧
        queue = Properties.contents addressWidth cycleState

private theorem evaluated_outputs_match (element : SignalType) (addressWidth : Nat)
    (inputs : (ports element).inputs.Values)
    (state : CycleState element addressWidth)
    (valid : Properties.Invariant addressWidth state) :
    (ports element).outputs.Matches
      (Reset.outputExpectations element addressWidth (Properties.contents addressWidth state))
      ((cycleContract element addressWidth).evaluate inputs state).1 := by
  let outputs := ((cycleContract element addressWidth).evaluate inputs state).1
  have evaluates := (cycleContract element addressWidth).evaluate_evaluatesTo
    inputs state
  rcases (outputRule_holds_iff element addressWidth inputs state outputs).mp
      (evaluates.1 .observe) with ⟨validEq, dataEq, readyEq⟩
  intro output
  cases output with
  | outputValid =>
      change BitExpectation.Matches _ _
      rw [Reset.outputExpectations]
      simp only [BitExpectation.exact_matches_iff]
      exact (Properties.outputValid_eq_contents_nonempty addressWidth state).symm.trans
        validEq.symm
  | inputReady =>
      change BitExpectation.Matches _ _
      rw [Reset.outputExpectations]
      simp only [BitExpectation.exact_matches_iff]
      simpa [Reset.inputReady, Reset.capacity,
        Properties.capacity, BitVector.cardinality_eq_pow] using
        (Properties.inputReady_eq_contents_below_capacity
          addressWidth state valid).symm.trans readyEq.symm
  | outputData =>
      cases equal : Properties.contents addressWidth state with
      | nil =>
          change element.Matches element.dontCareExpectation _
          exact SignalType.dontCareExpectation_matches _ _
      | cons head tail =>
          change element.Matches (element.exactExpectation head) _
          rw [SignalType.exactExpectation_matches_iff]
          exact (dataEq.trans (Properties.outputData_eq_contents_head
            addressWidth state head tail equal)).symm

private theorem readAdvance_eq (addressWidth : Nat)
    (inputs : (ports element).inputs.Values)
    (state : CycleState element addressWidth) :
    readAdvance (state .readPointer) (state .writePointer)
        (inputs .outputReady) =
      Reset.acceptsOutput (inputs .outputReady) (Properties.contents addressWidth state) := by
  change (outputValid (state .readPointer) (state .writePointer) &&
      inputs .outputReady) = _
  rw [Properties.outputValid_eq_contents_nonempty]
  simp [Reset.acceptsOutput, Reset.outputValid, Bool.and_comm]

private theorem writeAdvance_eq (addressWidth : Nat)
    (inputs : (ports element).inputs.Values)
    (state : CycleState element addressWidth)
    (valid : Properties.Invariant addressWidth state) :
    writeAdvance (state .readPointer) (state .writePointer)
        (inputs .inputValid) =
      Reset.acceptsInput addressWidth (inputs .inputValid)
        (Properties.contents addressWidth state) := by
  change (inputs .inputValid &&
      inputReady (state .readPointer) (state .writePointer)) = _
  rw [Properties.inputReady_eq_contents_below_capacity addressWidth state valid]
  simp [Reset.acceptsInput, Reset.inputReady, Reset.capacity,
    Properties.capacity, BitVector.cardinality_eq_pow]

@[simp] private theorem evaluated_next_readPointer (element : SignalType)
    (addressWidth : Nat) (inputs : (ports element).inputs.Values)
    (state : CycleState element addressWidth) :
    ((cycleContract element addressWidth).evaluate inputs state).2 .readPointer =
      nextReadPointer addressWidth (inputs .reset) (inputs .outputReady)
        (state .readPointer) (state .writePointer) := rfl

@[simp] private theorem evaluated_next_writePointer (element : SignalType)
    (addressWidth : Nat) (inputs : (ports element).inputs.Values)
    (state : CycleState element addressWidth) :
    ((cycleContract element addressWidth).evaluate inputs state).2 .writePointer =
      nextWritePointer addressWidth (inputs .reset) (inputs .inputValid)
        (state .readPointer) (state .writePointer) := rfl

@[simp] private theorem evaluated_next_entries (element : SignalType)
    (addressWidth : Nat) (inputs : (ports element).inputs.Values)
    (state : CycleState element addressWidth) :
    ((cycleContract element addressWidth).evaluate inputs state).2 .entries =
      nextEntries addressWidth (inputs .inputValid) (inputs .inputData)
        (state .readPointer) (state .writePointer) (state .entries) := rfl

private theorem evaluated_next_contents (element : SignalType) (addressWidth : Nat)
    (inputs : (ports element).inputs.Values)
    (state : CycleState element addressWidth)
    (valid : Properties.Invariant addressWidth state)
    (notReset : inputs .reset = false) :
    Properties.contents addressWidth
        ((cycleContract element addressWidth).evaluate inputs state).2 =
      Reset.nextQueue addressWidth (inputs .inputValid) (inputs .inputData)
        (inputs .outputReady) (Properties.contents addressWidth state) := by
  let readAccepted := Reset.acceptsOutput (inputs .outputReady)
    (Properties.contents addressWidth state)
  let writeAccepted := Reset.acceptsInput addressWidth (inputs .inputValid)
    (Properties.contents addressWidth state)
  have readEq := readAdvance_eq addressWidth inputs state
  have writeEq := writeAdvance_eq addressWidth inputs state valid
  cases readCase : readAccepted <;> cases writeCase : writeAccepted
  · have law := Properties.stalled_contents addressWidth (state .entries)
      (state .readPointer) (state .writePointer) (inputs .outputReady)
      (inputs .inputValid) (inputs .inputData) valid
      (by simpa [readAccepted, readCase] using readEq)
      (by simpa [writeAccepted, writeCase] using writeEq)
    rw [Reset.nextQueue_stall addressWidth (inputs .inputValid) (inputs .inputData)
      (inputs .outputReady) (Properties.contents addressWidth state) writeCase readCase]
    simpa [Properties.contents, notReset] using law
  · have law := Properties.enqueue_appends addressWidth (state .entries)
      (state .readPointer) (state .writePointer) (inputs .outputReady)
      (inputs .inputValid) (inputs .inputData) valid
      (by simpa [readAccepted, readCase] using readEq)
      (by simpa [writeAccepted, writeCase] using writeEq)
    rw [Reset.nextQueue_enqueue addressWidth (inputs .inputValid) (inputs .inputData)
      (inputs .outputReady) (Properties.contents addressWidth state) writeCase readCase]
    simpa [Properties.contents, notReset] using law
  · have law := Properties.dequeue_removes_oldest addressWidth (state .entries)
      (state .readPointer) (state .writePointer) (inputs .outputReady)
      (inputs .inputValid) (inputs .inputData) valid
      (by simpa [readAccepted, readCase] using readEq)
      (by simpa [writeAccepted, writeCase] using writeEq)
    rw [Reset.nextQueue_dequeue addressWidth (inputs .inputValid) (inputs .inputData)
      (inputs .outputReady) (Properties.contents addressWidth state) writeCase readCase]
    cases current : Properties.contents addressWidth state with
    | nil => simp [readAccepted, current, Reset.acceptsOutput] at readCase
    | cons head tail =>
        have dataHead := Properties.outputData_eq_contents_head addressWidth state head tail current
        change Properties.contents addressWidth state = _ at law
        rw [current, dataHead] at law
        have tailEq := (List.cons.inj law).2
        simpa [Properties.contents, notReset] using tailEq.symm
  · have law := Properties.simultaneous_transfer_preserves_order addressWidth
      (state .entries) (state .readPointer) (state .writePointer)
      (inputs .outputReady) (inputs .inputValid) (inputs .inputData) valid
      (by simpa [readAccepted, readCase] using readEq)
      (by simpa [writeAccepted, writeCase] using writeEq)
    rw [Reset.nextQueue_simultaneous addressWidth (inputs .inputValid) (inputs .inputData)
      (inputs .outputReady) (Properties.contents addressWidth state) writeCase readCase]
    cases current : Properties.contents addressWidth state with
    | nil => simp [readAccepted, current, Reset.acceptsOutput] at readCase
    | cons head tail =>
        have dataHead := Properties.outputData_eq_contents_head addressWidth state head tail current
        change Properties.contents addressWidth state ++ [inputs .inputData] = _ at law
        rw [current, dataHead] at law
        have tailEq := (List.cons.inj law).2
        simpa [Properties.contents, notReset] using tailEq.symm

private def executionInput (inputs : (ports element).inputs.Values) :
    Properties.Execution.Input element where
  enqValid := inputs .inputValid
  enqData := inputs .inputData
  deqReady := inputs .outputReady
  reset := inputs .reset

private theorem evaluated_next_preserves_invariant (element : SignalType)
    (addressWidth : Nat) (inputs : (ports element).inputs.Values)
    (state : CycleState element addressWidth)
    (valid : Properties.Invariant addressWidth state) :
    Properties.Invariant addressWidth
      ((cycleContract element addressWidth).evaluate inputs state).2 := by
  have inputEq : Properties.Execution.contractInputs element
      (executionInput inputs) = inputs := by
    funext input
    cases input <;> rfl
  have preserved := Properties.Execution.step_preserves_invariant element
    addressWidth state (executionInput inputs) valid
  change Properties.Invariant addressWidth
    ((cycleContract element addressWidth).evaluate
      (Properties.Execution.contractInputs element (executionInput inputs))
      state).2 at preserved
  rw [inputEq] at preserved
  exact preserved

private theorem evaluated_next_invariant_after_reset (element : SignalType)
    (addressWidth : Nat) (inputs : (ports element).inputs.Values)
    (state : CycleState element addressWidth) (reset : inputs .reset = true) :
    Properties.Invariant addressWidth
      ((cycleContract element addressWidth).evaluate inputs state).2 := by
  unfold Properties.Invariant
  rw [evaluated_next_readPointer, evaluated_next_writePointer]
  simp [reset, nextReadPointer, nextWritePointer,
    EnabledResetCounter.nextValue, Properties.occupancy,
    Properties.pointerValue, Properties.capacity,
    BitVector.cardinality_eq_pow,
    CircularBuffer.distance]

private theorem evaluated_next_contents_after_reset (element : SignalType)
    (addressWidth : Nat) (inputs : (ports element).inputs.Values)
    (state : CycleState element addressWidth) (reset : inputs .reset = true) :
    Properties.contents addressWidth
      ((cycleContract element addressWidth).evaluate inputs state).2 = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [Properties.contents_length]
  unfold Properties.occupancy
  rw [evaluated_next_readPointer, evaluated_next_writePointer]
  simp [reset, nextReadPointer, nextWritePointer,
    EnabledResetCounter.nextValue, Properties.pointerValue,
    CircularBuffer.distance]

private theorem refineExecution (element : SignalType) (addressWidth : Nat) :
    ∀ {initialState finalState :
        (certified element addressWidth).moduleStructure.State}
      {inputs : List (ports element).inputs.Values}
      {outputs : List (ports element).outputs.Values}
      {cycleState : CycleState element addressWidth}
      {synchronization : (resetContract element addressWidth).Synchronization},
      (certified element addressWidth).stateCorresponds
        cycleState initialState →
      Aligned element addressWidth cycleState synchronization →
      (certified element addressWidth).moduleStructure.Executes
        initialState inputs outputs finalState →
      ∃ finalCycleState finalSynchronization,
        (certified element addressWidth).stateCorresponds
          finalCycleState finalState ∧
        Aligned element addressWidth finalCycleState finalSynchronization ∧
        (resetContract element addressWidth).TraceMatches
          synchronization inputs outputs finalSynchronization := by
  intro initialState finalState inputs outputs cycleState synchronization
    corresponds aligned execution
  induction execution generalizing cycleState synchronization with
  | nil =>
      exact ⟨cycleState, synchronization, corresponds, aligned, .nil synchronization⟩
  | cons input output transition rest induction =>
      rcases transition with ⟨proposal, solution, outputEq, nextEq⟩
      rcases (certified element addressWidth).solution_matches_evaluate
          input cycleState _
          proposal corresponds solution with ⟨evaluatedOutputEq, nextCorresponds⟩
      have actualOutputEq : output =
          ((cycleContract element addressWidth).evaluate input cycleState).1 :=
        outputEq.symm.trans evaluatedOutputEq
      rw [nextEq] at nextCorresponds
      cases resetEq : input .reset
      · cases synchronization with
        | none =>
            rcases induction (synchronization := none) nextCorresponds trivial with
              ⟨finalCycleState, finalSynchronization, finalCorresponds,
                finalAligned, finalTrace⟩
            exact ⟨finalCycleState, finalSynchronization, finalCorresponds,
              finalAligned, .cons input output (.beforeReset resetEq) finalTrace⟩
        | some queue =>
            rcases aligned with ⟨valid, queueEq⟩
            have outputMatches := evaluated_outputs_match element addressWidth
              input cycleState valid
            have actualMatches : (ports element).outputs.Matches
                (Reset.outputExpectations element addressWidth queue) output := by
              rw [queueEq, actualOutputEq]
              exact outputMatches
            have nextContents := evaluated_next_contents element addressWidth
              input cycleState valid resetEq
            have nextValid := evaluated_next_preserves_invariant element
              addressWidth input cycleState valid
            rcases induction (synchronization := some
                (Reset.nextQueue addressWidth (input .inputValid)
                  (input .inputData) (input .outputReady) queue))
                nextCorresponds ⟨nextValid, by
                  change Reset.nextQueue addressWidth (input .inputValid)
                    (input .inputData) (input .outputReady) queue =
                      Properties.contents addressWidth
                        ((cycleContract element addressWidth).evaluate
                          input cycleState).2
                  rw [queueEq]
                  exact nextContents.symm⟩ with
              ⟨finalCycleState, finalSynchronization, finalCorresponds,
                finalAligned, finalTrace⟩
            exact ⟨finalCycleState, finalSynchronization, finalCorresponds,
              finalAligned, .cons input output
                (.ordinary resetEq actualMatches) finalTrace⟩
      · have nextValid := evaluated_next_invariant_after_reset element addressWidth
          input cycleState resetEq
        have nextEmpty := evaluated_next_contents_after_reset element addressWidth
          input cycleState resetEq
        rcases induction (synchronization := some []) nextCorresponds
            ⟨nextValid, nextEmpty.symm⟩ with
          ⟨finalCycleState, finalSynchronization, finalCorresponds,
            finalAligned, finalTrace⟩
        exact ⟨finalCycleState, finalSynchronization, finalCorresponds,
          finalAligned, .cons input output (.reset resetEq) finalTrace⟩

private theorem implementsResetContract (element : SignalType) (addressWidth : Nat) :
    ImplementsResetContract (moduleStructure element addressWidth)
      (resetContract element addressWidth) := by
  intro initialState inputs outputs finalState execution
  let cycleCertified := certified element addressWidth
  change cycleCertified.moduleStructure.Executes initialState inputs outputs
    finalState at execution
  rcases cycleCertified.hasCorrespondingState initialState with
    ⟨cycleState, corresponds⟩
  rcases refineExecution element addressWidth (synchronization := none)
      corresponds trivial execution with
    ⟨_, finalSynchronization, _, _, trace⟩
  exact ⟨finalSynchronization, trace⟩

noncomputable def resetCertified (element : SignalType) (addressWidth : Nat) :
    ModuleResetCertified (ports element) where
  moduleStructure := moduleStructure element addressWidth
  resetContract := resetContract element addressWidth
  hasSolution := (certified element addressWidth).hasStructuralResult
  implements := implementsResetContract element addressWidth

end Silean2.Modules.Fifo
