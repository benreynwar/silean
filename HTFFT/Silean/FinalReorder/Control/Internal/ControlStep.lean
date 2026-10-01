import HTFFT.Silean.FinalReorder.Control.Internal.ControlStructural

/-! One-cycle refinement of the concrete final-reorder controller. -/

namespace HTFFT.Silean.FinalReorder.Control.Internal

open _root_.Silean
open _root_.Silean.Modules

private abbrev CounterState (addressWidth : Nat) :=
  (EnabledResetCounter.cycleContract addressWidth
    (oneAddress addressWidth)).state.Values

def controlState (addressWidth : Nat)
    (writeCounter readCounter : CounterState addressWidth) : State addressWidth :=
  { storedWriteAddress := writeCounter .stored
    storedReadAddress := readCounter .stored }

private theorem lowBitLayout_apply (addressWidth : Nat)
    (address : Address addressWidth) :
    VectorLayout.apply (lowBitLayout addressWidth) address 0 =
      lowBit addressWidth address := by
  cases addressWidth with
  | zero => rfl
  | succ width => rfl

private theorem highBitLayout_apply (addressWidth : Nat)
    (address : Address addressWidth) :
    VectorLayout.apply (highBitLayout addressWidth) address 0 =
      highBit addressWidth address := by
  cases addressWidth with
  | zero => rfl
  | succ width =>
      simp only [highBitLayout, VectorLayout.apply, highBit]
      congr

theorem transition_of_solution (addressWidth : Nat)
    {step : HierStep (moduleStructure addressWidth)}
    (satisfies : (moduleStructure addressWidth).IsSolution step)
    {writeCurrent writeNext readCurrent readNext : CounterState addressWidth}
    (writeAllowed :
      (EnabledResetCounter.cycleContract addressWidth
        (oneAddress addressWidth)).Allows {
          inputs := (step.children .writeCounter).inputs
          currentState := writeCurrent
          outputs := (step.children .writeCounter).outputs
          nextState := writeNext })
    (readAllowed :
      (EnabledResetCounter.cycleContract addressWidth
        (oneAddress addressWidth)).Allows {
          inputs := (step.children .readCounter).inputs
          currentState := readCurrent
          outputs := (step.children .readCounter).outputs
          nextState := readNext }) :
    Transition addressWidth step.inputs
      (controlState addressWidth writeCurrent readCurrent) step.outputs
      (controlState addressWidth writeNext readNext) := by
  have trueRealizes := ModuleStructure.child_realizes satisfies .trueSource
  have zeroRealizes := ModuleStructure.child_realizes satisfies .zeroAddress
  have lastRealizes := ModuleStructure.child_realizes satisfies .lastAddress
  have writeMuxRealizes := ModuleStructure.child_realizes satisfies .writeSelect
  have readMuxRealizes := ModuleStructure.child_realizes satisfies .readSelect
  have lowLayoutRealizes := ModuleStructure.child_realizes satisfies .lowSelect
  have highLayoutRealizes := ModuleStructure.child_realizes satisfies .highSelect
  have lowNotRealizes := ModuleStructure.child_realizes satisfies .lowInvert
  have equalityRealizes := ModuleStructure.child_realizes satisfies .bypass
  simp only [structuralChildren] at trueRealizes zeroRealizes lastRealizes
  simp only [structuralChildren] at writeMuxRealizes readMuxRealizes
  simp only [structuralChildren] at lowLayoutRealizes highLayoutRealizes
  simp only [structuralChildren] at lowNotRealizes equalityRealizes

  obtain ⟨_, _, trueAllowed⟩ :=
    Constant.allowed_of_realization .bit true trueRealizes
  obtain ⟨_, _, zeroAllowed⟩ := Constant.allowed_of_realization
    (.vector addressWidth .bit) (zeroAddress addressWidth) zeroRealizes
  obtain ⟨_, _, lastAllowed⟩ := Constant.allowed_of_realization
    (.vector addressWidth .bit) (lastAddress addressWidth) lastRealizes
  have trueOutput := Constant.output_of_allowed .bit true trueAllowed
  have zeroOutput := Constant.output_of_allowed (.vector addressWidth .bit)
    (zeroAddress addressWidth) zeroAllowed
  have lastOutput := Constant.output_of_allowed (.vector addressWidth .bit)
    (lastAddress addressWidth) lastAllowed
  have writeCounterOutput := EnabledResetCounter.value_of_allowed writeAllowed
  have readCounterOutput := EnabledResetCounter.value_of_allowed readAllowed
  have writeNextEq := EnabledResetCounter.next_stored_of_allowed writeAllowed
  have readNextEq := EnabledResetCounter.next_stored_of_allowed readAllowed
  have writeMuxOutput := Mux.result_of_realization
    (.vector addressWidth .bit) writeMuxRealizes
  have readMuxOutput := Mux.result_of_realization
    (.vector addressWidth .bit) readMuxRealizes
  have lowLayoutOutput := VectorLayout.output_of_realization addressWidth 1
    (lowBitLayout addressWidth) lowLayoutRealizes
  have highLayoutOutput := VectorLayout.output_of_realization addressWidth 1
    (highBitLayout addressWidth) highLayoutRealizes

  have splitOutputs := ModuleStructure.splitter_outputs_of_solution
    (by simpa only [structuralChildren] using
      ModuleStructure.child_isSolution satisfies .writeSplit)
  have lowSplitOutputs := ModuleStructure.splitter_outputs_of_solution
    (by simpa only [structuralChildren] using
      ModuleStructure.child_isSolution satisfies .lowSplit)
  have highSplitOutputs := ModuleStructure.splitter_outputs_of_solution
    (by simpa only [structuralChildren] using
      ModuleStructure.child_isSolution satisfies .highSplit)
  have write0Outputs := ModuleStructure.combiner_outputs_of_solution
    (by simpa only [structuralChildren] using
      ModuleStructure.child_isSolution satisfies .writeAddress0)
  have write1Outputs := ModuleStructure.combiner_outputs_of_solution
    (by simpa only [structuralChildren] using
      ModuleStructure.child_isSolution satisfies .writeAddress1)

  have writeEnable := ModuleStructure.child_input satisfies .writeCounter .enable
  have readEnable := ModuleStructure.child_input satisfies .readCounter .enable
  have writeReset := ModuleStructure.child_input satisfies .writeCounter .reset
  have readReset := ModuleStructure.child_input satisfies .readCounter .reset
  have writeMuxSelect := ModuleStructure.child_input satisfies .writeSelect .select
  have writeMuxFalse := ModuleStructure.child_input satisfies .writeSelect .whenFalse
  have writeMuxTrue := ModuleStructure.child_input satisfies .writeSelect .whenTrue
  have readMuxSelect := ModuleStructure.child_input satisfies .readSelect .select
  have readMuxFalse := ModuleStructure.child_input satisfies .readSelect .whenFalse
  have readMuxTrue := ModuleStructure.child_input satisfies .readSelect .whenTrue
  have splitInput := ModuleStructure.child_input satisfies .writeSplit .value
  have lowLayoutInput := ModuleStructure.child_input satisfies .lowSelect .input
  have highLayoutInput := ModuleStructure.child_input satisfies .highSelect .input
  have lowSplitInput := ModuleStructure.child_input satisfies .lowSplit .value
  have highSplitInput := ModuleStructure.child_input satisfies .highSplit .value
  have lowNotInput := ModuleStructure.child_input satisfies .lowInvert .input

  change (step.children .trueSource).outputs .output = true at trueOutput
  change (step.children .zeroAddress).outputs .output =
    zeroAddress addressWidth at zeroOutput
  change (step.children .lastAddress).outputs .output =
    lastAddress addressWidth at lastOutput
  change (step.children .writeCounter).outputs .value =
    writeCurrent .stored at writeCounterOutput
  change (step.children .readCounter).outputs .value =
    readCurrent .stored at readCounterOutput
  change (step.children .writeSelect).outputs .result =
    bif (step.children .writeSelect).inputs .select then
      (step.children .writeSelect).inputs .whenTrue
    else (step.children .writeSelect).inputs .whenFalse at writeMuxOutput
  change (step.children .readSelect).outputs .result =
    bif (step.children .readSelect).inputs .select then
      (step.children .readSelect).inputs .whenTrue
    else (step.children .readSelect).inputs .whenFalse at readMuxOutput

  change (step.children .writeCounter).inputs .enable =
    (step.children .trueSource).outputs .output at writeEnable
  change (step.children .readCounter).inputs .enable =
    (step.children .trueSource).outputs .output at readEnable
  change (step.children .writeCounter).inputs .reset =
    step.inputs .i_first at writeReset
  change (step.children .readCounter).inputs .reset =
    step.inputs .i_readFirst at readReset
  change (step.children .writeSelect).inputs .select =
    step.inputs .i_first at writeMuxSelect
  change (step.children .writeSelect).inputs .whenFalse =
    (step.children .writeCounter).outputs .value at writeMuxFalse
  change (step.children .writeSelect).inputs .whenTrue =
    (step.children .zeroAddress).outputs .output at writeMuxTrue
  change (step.children .readSelect).inputs .select =
    step.inputs .i_readFirst at readMuxSelect
  change (step.children .readSelect).inputs .whenFalse =
    (step.children .readCounter).outputs .value at readMuxFalse
  change (step.children .readSelect).inputs .whenTrue =
    (step.children .zeroAddress).outputs .output at readMuxTrue
  change (step.children .writeSplit).inputs .value =
    (step.children .writeSelect).outputs .result at splitInput
  change (step.children .lowSelect).inputs .input =
    (step.children .writeSelect).outputs .result at lowLayoutInput
  change (step.children .highSelect).inputs .input =
    (step.children .readSelect).outputs .result at highLayoutInput
  change (step.children .lowSplit).inputs .value =
    (step.children .lowSelect).outputs .output at lowSplitInput
  change (step.children .highSplit).inputs .value =
    (step.children .highSelect).outputs .output at highSplitInput
  change (step.children .lowInvert).inputs .input =
    (step.children .lowSplit).outputs 0 at lowNotInput

  let current := controlState addressWidth writeCurrent readCurrent
  let write := effectiveAddress addressWidth (step.inputs .i_first)
    current.storedWriteAddress
  let read := effectiveAddress addressWidth (step.inputs .i_readFirst)
    current.storedReadAddress

  have writeOutput :
      (step.children .writeSelect).outputs .result = write := by
    rw [writeMuxOutput, writeMuxSelect, writeMuxFalse, writeMuxTrue,
      zeroOutput, writeCounterOutput]
    rfl

  have readSelectOutput :
      (step.children .readSelect).outputs .result = read := by
    rw [readMuxOutput, readMuxSelect, readMuxFalse, readMuxTrue,
      zeroOutput, readCounterOutput]
    rfl

  have writeSplitAt (index : Fin addressWidth) :
      (step.children .writeSplit).outputs index = write index := by
    have component := congrFun splitOutputs index
    simpa [Composition.SignalSplitter.outputValues, splitInput,
      writeOutput] using component

  have lowOutput : (step.children .lowSplit).outputs 0 =
      lowBit addressWidth write := by
    have component := congrFun lowSplitOutputs (0 : Fin 1)
    rw [show (step.children .lowSplit).outputs 0 =
        (step.children .lowSplit).inputs .value 0 by
      simpa [Composition.SignalSplitter.outputValues] using component]
    rw [lowSplitInput]
    have layoutAt := congrFun lowLayoutOutput (0 : Fin 1)
    change (step.children .lowSelect).outputs .output 0 =
      VectorLayout.apply (lowBitLayout addressWidth)
        ((step.children .lowSelect).inputs .input) 0 at layoutAt
    rw [layoutAt, lowLayoutInput, writeOutput]
    exact lowBitLayout_apply addressWidth write

  have highOutput : (step.children .highSplit).outputs 0 =
      highBit addressWidth read := by
    have component := congrFun highSplitOutputs (0 : Fin 1)
    rw [show (step.children .highSplit).outputs 0 =
        (step.children .highSplit).inputs .value 0 by
      simpa [Composition.SignalSplitter.outputValues] using component]
    rw [highSplitInput]
    have layoutAt := congrFun highLayoutOutput (0 : Fin 1)
    change (step.children .highSelect).outputs .output 0 =
      VectorLayout.apply (highBitLayout addressWidth)
        ((step.children .highSelect).inputs .input) 0 at layoutAt
    rw [layoutAt, highLayoutInput, readSelectOutput]
    exact highBitLayout_apply addressWidth read

  have lowNotOutput : (step.children .lowInvert).outputs .output =
      !lowBit addressWidth write := by
    have output : (step.children .lowInvert).outputs .output =
        !(step.children .lowInvert).inputs .input := by
      let certification := Primitives.notCertified.certification
      obtain ⟨contractState, corresponds⟩ := certification.hasCorrespondingState
        (step.children .lowInvert).currentState
      obtain ⟨_, allowed, _⟩ := certification.allows_of_realizes contractState
        (step.children .lowInvert).step corresponds lowNotRealizes
      exact (Primitives.notOutputRule_holds_iff _ _ _).mp
        (allowed.1 .apply)
    rw [output, lowNotInput, lowOutput]

  have write0Output : (step.children .writeAddress0).outputs .value =
      writeAddress0 addressWidth write := by
    funext index
    have combineAt := congrFun (congrFun write0Outputs .value) index
    have combineInput := ModuleStructure.child_input satisfies .writeAddress0 index
    change (step.children .writeAddress0).outputs .value index =
      (step.children .writeAddress0).inputs index at combineAt
    rw [combineAt]
    by_cases nextInRange : index.val + 1 < addressWidth
    · simp only [wiring, nextInRange, dite_true,
        EndpointContext.instanceOutput_value]
        at combineInput
      rw [combineInput, writeSplitAt]
      simp [writeAddress0, nextInRange]
    · simp only [wiring, nextInRange, dite_false,
        EndpointContext.instanceOutput_value]
        at combineInput
      rw [combineInput, writeSplitAt]
      simp [writeAddress0, nextInRange]

  have write1Output : (step.children .writeAddress1).outputs .value =
      writeAddress1 addressWidth write := by
    funext index
    have combineAt := congrFun (congrFun write1Outputs .value) index
    have combineInput := ModuleStructure.child_input satisfies .writeAddress1 index
    change (step.children .writeAddress1).outputs .value index =
      (step.children .writeAddress1).inputs index at combineAt
    rw [combineAt]
    by_cases nextInRange : index.val + 1 < addressWidth
    · simp only [wiring, nextInRange, dite_true,
        EndpointContext.instanceOutput_value]
        at combineInput
      rw [combineInput, writeSplitAt]
      simp [writeAddress1, nextInRange]
    · simp only [wiring, nextInRange, dite_false,
        EndpointContext.instanceOutput_value]
        at combineInput
      rw [combineInput, lowNotOutput]
      have positive : 0 < addressWidth := Nat.zero_lt_of_lt index.isLt
      simp [writeAddress1, nextInRange, lowBit, positive]

  have allOutput : (step.children .bypass).outputs .result =
      bypass addressWidth write := by
    have result := Equality.result_of_realization
      (.vector addressWidth .bit) equalityRealizes
    have leftInput := ModuleStructure.child_input satisfies .bypass .left
    have rightInput := ModuleStructure.child_input satisfies .bypass .right
    change (step.children .bypass).outputs .result =
      (SignalType.vector addressWidth .bit).equal
        ((step.children .bypass).inputs .left)
        ((step.children .bypass).inputs .right) at result
    change (step.children .bypass).inputs .left =
      (step.children .writeSelect).outputs .result at leftInput
    change (step.children .bypass).inputs .right =
      (step.children .lastAddress).outputs .output at rightInput
    rw [result, leftInput, rightInput, writeOutput, lastOutput]
    rfl

  have nextWrite : writeNext .stored =
      _root_.Silean.Modules.Increment.incrementValue addressWidth write := by
    change writeNext .stored = EnabledResetCounter.nextValue addressWidth
      (oneAddress addressWidth) ((step.children .writeCounter).inputs .enable)
      ((step.children .writeCounter).inputs .reset) (writeCurrent .stored)
      at writeNextEq
    rw [writeNextEq, writeEnable, trueOutput, writeReset]
    cases first : step.inputs .i_first <;>
      simp [EnabledResetCounter.nextValue, write, effectiveAddress,
        current, controlState, first]

  have nextRead : readNext .stored =
      _root_.Silean.Modules.Increment.incrementValue addressWidth read := by
    change readNext .stored = EnabledResetCounter.nextValue addressWidth
      (oneAddress addressWidth) ((step.children .readCounter).inputs .enable)
      ((step.children .readCounter).inputs .reset) (readCurrent .stored)
      at readNextEq
    rw [readNextEq, readEnable, trueOutput, readReset]
    cases first : step.inputs .i_readFirst <;>
      simp [EnabledResetCounter.nextValue, read, effectiveAddress,
        current, controlState, first]

  have write0Boundary := ModuleStructure.parent_output satisfies .o_writeAddress0
  have write1Boundary := ModuleStructure.parent_output satisfies .o_writeAddress1
  have readBoundary := ModuleStructure.parent_output satisfies .o_readAddress
  have writeSwapBoundary := ModuleStructure.parent_output satisfies .o_writeSwap
  have readSwapBoundary := ModuleStructure.parent_output satisfies .o_readSwap
  have bypassBoundary := ModuleStructure.parent_output satisfies .o_bypass
  change step.outputs .o_writeAddress0 =
    (step.children .writeAddress0).outputs .value at write0Boundary
  change step.outputs .o_writeAddress1 =
    (step.children .writeAddress1).outputs .value at write1Boundary
  change step.outputs .o_readAddress =
    (step.children .readSelect).outputs .result at readBoundary
  change step.outputs .o_writeSwap =
    (step.children .lowSplit).outputs 0 at writeSwapBoundary
  change step.outputs .o_readSwap =
    (step.children .highSplit).outputs 0 at readSwapBoundary
  change step.outputs .o_bypass =
    (step.children .bypass).outputs .result at bypassBoundary

  constructor
  · exact ⟨write0Boundary.trans write0Output,
      write1Boundary.trans write1Output,
      readBoundary.trans (by simpa [readAddress] using readSelectOutput),
      writeSwapBoundary.trans lowOutput,
      readSwapBoundary.trans highOutput,
      bypassBoundary.trans allOutput⟩
  · apply State.ext
    · exact nextWrite
    · exact nextRead

end HTFFT.Silean.FinalReorder.Control.Internal
