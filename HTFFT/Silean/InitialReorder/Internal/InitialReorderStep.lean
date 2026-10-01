import HTFFT.Silean.InitialReorder.Internal.InitialReorderStructure
import HTFFT.Silean.InitialReorder.Lane.LaneDerived
import Silean.Modules.ConditionalNegate.ConditionalNegateDerived
import Silean.Modules.VectorReindex.VectorReindexDerived

/-! Public child-interface equations for one concrete initial-reorder step. -/

namespace HTFFT.Silean.InitialReorder.Internal
open FFT

open _root_.Silean
open _root_.Silean.Modules

private abbrev reorderStructure (depth : Nat)
    (configuration : Configuration depth) :=
  InitialReorder.moduleStructure depth configuration

theorem controlInput_of_solution
    {step : HierStep (reorderStructure depth configuration)}
    (satisfies : (reorderStructure depth configuration).IsSolution step) :
    (step.children .control).inputs .i_first = step.inputs .i_first :=
  ModuleStructure.child_input satisfies .control .i_first

theorem markerWiring_of_solution
    {step : HierStep (reorderStructure depth configuration)}
    (satisfies : (reorderStructure depth configuration).IsSolution step) :
    (step.children .markerAlign).inputs .input = step.inputs .i_first ∧
      step.outputs .o_first =
        (step.children .markerAlign).outputs .output :=
  ⟨ModuleStructure.child_input satisfies .markerAlign .input,
    ModuleStructure.parent_output satisfies .o_first⟩

/-- The combinational write-side preparation presents the barrel shifter with
the natural negative rotation and one naturally tagged payload per input
lane. -/
theorem writeBarrelInputs_of_solution
    {step : HierStep (reorderStructure depth configuration)}
    (satisfies : (reorderStructure depth configuration).IsSolution step) :
    (step.children .preBarrel).inputs .shift =
        InitialReorder.preRotation configuration
          ((step.children .control).outputs .o_address) ∧
      (step.children .preBarrel).inputs .data = fun lane =>
        InitialReorder.Lane.resultValue configuration lane
          (step.inputs .i_data lane)
          ((step.children .control).outputs .o_address)
          ((step.children .control).outputs .o_reversed) := by
  have rotationRealizes := ModuleStructure.child_realizes satisfies .laneRotation
  have negateRealizes := ModuleStructure.child_realizes satisfies .preRotation
  have splitSolution := ModuleStructure.child_isSolution satisfies .preSplit
  have combineSolution := ModuleStructure.child_isSolution satisfies
    .payloadCombine
  simp only [InitialReorder.structuralChildren] at rotationRealizes
  simp only [InitialReorder.structuralChildren] at negateRealizes
  simp only [InitialReorder.structuralChildren] at splitSolution
  simp only [InitialReorder.structuralChildren] at combineSolution
  have rotationValue := VectorReindex.output_of_realization .bit
    (InitialReorder.addressWidth configuration) configuration.laneDepth
    (laneRotationLayout configuration) rotationRealizes
  have negateValue := ConditionalNegate.result_of_realization
    configuration.laneDepth negateRealizes
  have splitValue := ModuleStructure.splitter_outputs_of_solution splitSolution
  have combineValue := ModuleStructure.combiner_outputs_of_solution
    combineSolution
  have rotationInput := ModuleStructure.child_input satisfies .laneRotation .input
  have negateInput := ModuleStructure.child_input satisfies .preRotation .value
  have negateSelect := ModuleStructure.child_input satisfies .preRotation .negate
  have trueRealizes := ModuleStructure.child_realizes satisfies .trueSource
  simp only [InitialReorder.structuralChildren] at trueRealizes
  obtain ⟨_, _, trueAllowed⟩ := Constant.allowed_of_realization .bit true
    trueRealizes
  have trueValue := Constant.output_of_allowed .bit true trueAllowed
  have splitInput := ModuleStructure.child_input satisfies .preSplit .value
  have barrelShift := ModuleStructure.child_input satisfies .preBarrel .shift
  have barrelData := ModuleStructure.child_input satisfies .preBarrel .data
  change (step.children .laneRotation).inputs .input =
    (step.children .control).outputs .o_address at rotationInput
  change (step.children .preRotation).inputs .value =
    (step.children .laneRotation).outputs .output at negateInput
  change (step.children .preRotation).inputs .negate =
    (step.children .trueSource).outputs .output at negateSelect
  change (step.children .preSplit).inputs .value = step.inputs .i_data
    at splitInput
  change (step.children .preBarrel).inputs .shift =
    (step.children .preRotation).outputs .result at barrelShift
  change (step.children .preBarrel).inputs .data =
    (step.children .payloadCombine).outputs .value at barrelData
  change (step.children .laneRotation).outputs .output =
    VectorReindex.apply (laneRotationLayout configuration)
      ((step.children .laneRotation).inputs .input) at rotationValue
  change (step.children .preRotation).outputs .result =
    ConditionalNegate.resultValue configuration.laneDepth
      ((step.children .preRotation).inputs .value)
      ((step.children .preRotation).inputs .negate) at negateValue
  change (step.children .trueSource).outputs .output = true at trueValue
  constructor
  · rw [barrelShift, negateValue, negateInput, rotationValue, rotationInput]
    rw [negateSelect, trueValue]
    rfl
  · rw [barrelData]
    funext lane
    have laneSolution := ModuleStructure.child_isSolution satisfies
      (.addressPayload lane)
    simp only [InitialReorder.structuralChildren] at laneSolution
    have laneValue := InitialReorder.Lane.result_of_solution depth configuration
      lane laneSolution
    have laneData := ModuleStructure.child_input satisfies
      (.addressPayload lane) .i_data
    have laneAddress := ModuleStructure.child_input satisfies
      (.addressPayload lane) .i_cycleAddress
    have laneReversed := ModuleStructure.child_input satisfies
      (.addressPayload lane) .i_reversed
    have combineLane := ModuleStructure.child_input satisfies
      .payloadCombine lane
    have combineAt : (step.children .payloadCombine).outputs .value lane =
        (step.children .payloadCombine).inputs lane :=
      congrFun (congrFun combineValue .value) lane
    have splitAt : (step.children .preSplit).outputs lane =
        (step.children .preSplit).inputs .value lane :=
      congrFun splitValue lane
    change (step.children (.addressPayload lane)).inputs .i_data =
      (step.children .preSplit).outputs lane at laneData
    change (step.children (.addressPayload lane)).inputs .i_cycleAddress =
      (step.children .control).outputs .o_address at laneAddress
    change (step.children (.addressPayload lane)).inputs .i_reversed =
      (step.children .control).outputs .o_reversed at laneReversed
    change (step.children .payloadCombine).inputs lane =
      (step.children (.addressPayload lane)).outputs .o_payload at combineLane
    rw [combineAt, combineLane, laneValue, laneData,
      splitAt, splitInput, laneAddress, laneReversed]

/-- The three frame-delay paths sample the current controller coordinate and
its natural lane rotation in the same cycle. -/
theorem readAlignInputs_of_solution
    {step : HierStep (reorderStructure depth configuration)}
    (satisfies : (reorderStructure depth configuration).IsSolution step) :
    (step.children .readCycleAlign).inputs .input =
        (step.children .control).outputs .o_address ∧
      (step.children .readOrientationAlign).inputs .input =
        (step.children .control).outputs .o_reversed ∧
      (step.children .readRotationAlign).inputs .input =
        InitialReorder.laneRotation configuration
          ((step.children .control).outputs .o_address) := by
  have cycleInput := ModuleStructure.child_input satisfies
    .readCycleAlign .input
  have orientationInput := ModuleStructure.child_input satisfies
    .readOrientationAlign .input
  have rotationInput := ModuleStructure.child_input satisfies
    .readRotationAlign .input
  have laneRotationInput := ModuleStructure.child_input satisfies
    .laneRotation .input
  have laneRotationRealizes := ModuleStructure.child_realizes satisfies
    .laneRotation
  simp only [InitialReorder.structuralChildren] at laneRotationRealizes
  have laneRotationOutput := VectorReindex.output_of_realization .bit
    (InitialReorder.addressWidth configuration) configuration.laneDepth
    (laneRotationLayout configuration) laneRotationRealizes
  change (step.children .readCycleAlign).inputs .input =
    (step.children .control).outputs .o_address at cycleInput
  change (step.children .readOrientationAlign).inputs .input =
    (step.children .control).outputs .o_reversed at orientationInput
  change (step.children .readRotationAlign).inputs .input =
    (step.children .laneRotation).outputs .output at rotationInput
  change (step.children .laneRotation).inputs .input =
    (step.children .control).outputs .o_address at laneRotationInput
  change (step.children .laneRotation).outputs .output =
    VectorReindex.apply (laneRotationLayout configuration)
      ((step.children .laneRotation).inputs .input) at laneRotationOutput
  refine ⟨cycleInput, orientationInput, ?_⟩
  rw [rotationInput, laneRotationOutput, laneRotationInput]
  rfl

/-- The independent read path presents one address per logical output lane,
using the delayed controller address and the opposite delayed orientation. -/
theorem readBarrelInputs_of_solution
    {step : HierStep (reorderStructure depth configuration)}
    (satisfies : (reorderStructure depth configuration).IsSolution step) :
    (step.children .readPreBarrel).inputs .shift =
        ConditionalNegate.resultValue configuration.laneDepth
          ((step.children .readRotationAlign).outputs .output) true ∧
      (step.children .readPreBarrel).inputs .data = fun lane =>
        InitialReorder.Lane.memoryAddress configuration lane
          ((step.children .readCycleAlign).outputs .output)
          (!((step.children .readOrientationAlign).outputs .output)) := by
  have negateRealizes := ModuleStructure.child_realizes satisfies .readPreRotation
  have invertSolution := ModuleStructure.child_isSolution satisfies
    .readOrientationInvert
  have combineSolution := ModuleStructure.child_isSolution satisfies
    .readAddressCombine
  simp only [InitialReorder.structuralChildren] at negateRealizes
  simp only [InitialReorder.structuralChildren] at invertSolution
  simp only [InitialReorder.structuralChildren] at combineSolution
  have negateValue := ConditionalNegate.result_of_realization
    configuration.laneDepth negateRealizes
  have invertValue :
      (step.children .readOrientationInvert).outputs .output =
        !((step.children .readOrientationInvert).inputs .input) := by
    exact congrFun invertSolution.1 .output
  have combineValue := ModuleStructure.combiner_outputs_of_solution
    combineSolution
  have negateInput := ModuleStructure.child_input satisfies .readPreRotation .value
  have negateSelect := ModuleStructure.child_input satisfies
    .readPreRotation .negate
  have trueRealizes := ModuleStructure.child_realizes satisfies .trueSource
  simp only [InitialReorder.structuralChildren] at trueRealizes
  obtain ⟨_, _, trueAllowed⟩ := Constant.allowed_of_realization .bit true
    trueRealizes
  have trueValue := Constant.output_of_allowed .bit true trueAllowed
  have barrelShift := ModuleStructure.child_input satisfies .readPreBarrel .shift
  have barrelData := ModuleStructure.child_input satisfies .readPreBarrel .data
  change (step.children .readPreRotation).inputs .value =
    (step.children .readRotationAlign).outputs .output at negateInput
  change (step.children .readPreRotation).inputs .negate =
    (step.children .trueSource).outputs .output at negateSelect
  change (step.children .readPreBarrel).inputs .shift =
    (step.children .readPreRotation).outputs .result at barrelShift
  change (step.children .readPreBarrel).inputs .data =
    (step.children .readAddressCombine).outputs .value at barrelData
  change (step.children .readPreRotation).outputs .result =
    ConditionalNegate.resultValue configuration.laneDepth
      ((step.children .readPreRotation).inputs .value)
      ((step.children .readPreRotation).inputs .negate) at negateValue
  change (step.children .trueSource).outputs .output = true at trueValue
  constructor
  · rw [barrelShift, negateValue, negateInput, negateSelect, trueValue]
  · rw [barrelData]
    funext lane
    have laneSolution := ModuleStructure.child_isSolution satisfies
      (.readAddressPayload lane)
    simp only [InitialReorder.structuralChildren] at laneSolution
    have laneValue := InitialReorder.Lane.address_of_solution depth configuration
      lane laneSolution
    have laneCycle := ModuleStructure.child_input satisfies
      (.readAddressPayload lane) .i_cycleAddress
    have laneReversed := ModuleStructure.child_input satisfies
      (.readAddressPayload lane) .i_reversed
    have invertInput := ModuleStructure.child_input satisfies
      .readOrientationInvert .input
    have combineLane := ModuleStructure.child_input satisfies
      .readAddressCombine lane
    have combineAt :
        (step.children .readAddressCombine).outputs .value lane =
          (step.children .readAddressCombine).inputs lane :=
      congrFun (congrFun combineValue .value) lane
    change (step.children (.readAddressPayload lane)).inputs .i_cycleAddress =
      (step.children .readCycleAlign).outputs .output at laneCycle
    change (step.children (.readAddressPayload lane)).inputs .i_reversed =
      (step.children .readOrientationInvert).outputs .output at laneReversed
    change (step.children .readOrientationInvert).inputs .input =
      (step.children .readOrientationAlign).outputs .output at invertInput
    change (step.children .readAddressCombine).inputs lane =
      (step.children (.readAddressPayload lane)).outputs .o_address
      at combineLane
    rw [combineAt, combineLane, laneValue, laneCycle,
      laneReversed, invertValue, invertInput]

theorem bankInputs_of_solution
    {step : HierStep (reorderStructure depth configuration)}
    (satisfies : (reorderStructure depth configuration).IsSolution step)
    (lane : Fin (laneCount configuration)) :
    (step.children (.bank lane)).inputs .i_writePayload =
        (step.children .preBarrel).outputs .result lane ∧
      (step.children (.bank lane)).inputs .i_readAddress =
        (step.children .readPreBarrel).outputs .result lane := by
  have payloadSplitSolution := ModuleStructure.child_isSolution satisfies
    .payloadSplit
  have addressSplitSolution := ModuleStructure.child_isSolution satisfies
    .readAddressSplit
  simp only [InitialReorder.structuralChildren] at payloadSplitSolution
  simp only [InitialReorder.structuralChildren] at addressSplitSolution
  have payloadSplitValue := ModuleStructure.splitter_outputs_of_solution
    payloadSplitSolution
  have addressSplitValue := ModuleStructure.splitter_outputs_of_solution
    addressSplitSolution
  have payloadSplitInput := ModuleStructure.child_input satisfies
    .payloadSplit .value
  have addressSplitInput := ModuleStructure.child_input satisfies
    .readAddressSplit .value
  have bankWrite := ModuleStructure.child_input satisfies
    (.bank lane) .i_writePayload
  have bankRead := ModuleStructure.child_input satisfies
    (.bank lane) .i_readAddress
  change (step.children .payloadSplit).inputs .value =
    (step.children .preBarrel).outputs .result at payloadSplitInput
  change (step.children .readAddressSplit).inputs .value =
    (step.children .readPreBarrel).outputs .result at addressSplitInput
  change (step.children (.bank lane)).inputs .i_writePayload =
    (step.children .payloadSplit).outputs lane at bankWrite
  change (step.children (.bank lane)).inputs .i_readAddress =
    (step.children .readAddressSplit).outputs lane at bankRead
  constructor
  · have splitAt : (step.children .payloadSplit).outputs lane =
        (step.children .payloadSplit).inputs .value lane :=
      congrFun payloadSplitValue lane
    rw [bankWrite, splitAt, payloadSplitInput]
  · have splitAt : (step.children .readAddressSplit).outputs lane =
        (step.children .readAddressSplit).inputs .value lane :=
      congrFun addressSplitValue lane
    rw [bankRead, splitAt, addressSplitInput]

theorem postRotationInput_of_solution
    {step : HierStep (reorderStructure depth configuration)}
    (satisfies : (reorderStructure depth configuration).IsSolution step) :
    (step.children .postRotationAlign).inputs .input =
      (step.children .readRotationAlign).outputs .output :=
  ModuleStructure.child_input satisfies .postRotationAlign .input

theorem postBarrelInputs_of_solution
    {step : HierStep (reorderStructure depth configuration)}
    (satisfies : (reorderStructure depth configuration).IsSolution step) :
    (step.children .postBarrel).inputs .shift =
        (step.children .postRotationAlign).outputs .output ∧
      (step.children .postBarrel).inputs .data = fun lane =>
        (step.children (.bank lane)).outputs .o_data := by
  have combineSolution := ModuleStructure.child_isSolution satisfies .bankCombine
  simp only [InitialReorder.structuralChildren] at combineSolution
  have combineValue := ModuleStructure.combiner_outputs_of_solution
    combineSolution
  have postShift := ModuleStructure.child_input satisfies .postBarrel .shift
  have postData := ModuleStructure.child_input satisfies .postBarrel .data
  change (step.children .postBarrel).inputs .shift =
    (step.children .postRotationAlign).outputs .output at postShift
  change (step.children .postBarrel).inputs .data =
    (step.children .bankCombine).outputs .value at postData
  constructor
  · exact postShift
  · rw [postData]
    funext lane
    have combineLane := ModuleStructure.child_input satisfies .bankCombine lane
    have combineAt : (step.children .bankCombine).outputs .value lane =
        (step.children .bankCombine).inputs lane :=
      congrFun (congrFun combineValue .value) lane
    change (step.children .bankCombine).inputs lane =
      (step.children (.bank lane)).outputs .o_data at combineLane
    rw [combineAt, combineLane]

theorem dataOutput_of_solution
    {step : HierStep (reorderStructure depth configuration)}
    (satisfies : (reorderStructure depth configuration).IsSolution step) :
    step.outputs .o_data = (step.children .postBarrel).outputs .result :=
  ModuleStructure.parent_output satisfies .o_data

end HTFFT.Silean.InitialReorder.Internal
