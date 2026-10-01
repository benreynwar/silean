import HTFFT.Silean.FinalReorder.Internal.FinalReorderStructure

/-! Public child-interface equations for one concrete final-reorder step. -/

namespace HTFFT.Silean.FinalReorder.Internal
open FFT

open _root_.Silean
open _root_.Silean.Modules

private abbrev reorderStructure (depth : Nat)
    (configuration : Configuration depth) :=
  FinalReorder.moduleStructure depth configuration

theorem markerAndControl_of_solution
    {step : HierStep (reorderStructure depth configuration)}
    (satisfies : (reorderStructure depth configuration).IsSolution step) :
    (step.children .markerDelay).inputs .input = step.inputs .i_first ∧
      step.outputs .o_first =
        (step.children .markerDelay).outputs .output ∧
      (step.children .control).inputs .i_first = step.inputs .i_first ∧
      (step.children .control).inputs .i_readFirst =
        (step.children .markerDelay).outputs .output := by
  exact ⟨ModuleStructure.child_input satisfies .markerDelay .input,
    ModuleStructure.parent_output satisfies .o_first,
    ModuleStructure.child_input satisfies .control .i_first,
    ModuleStructure.child_input satisfies .control .i_readFirst⟩

theorem bank0Inputs_of_solution
    {step : HierStep (reorderStructure depth configuration)}
    (satisfies : (reorderStructure depth configuration).IsSolution step) :
    (step.children .bank0).inputs .writeEnable = true ∧
      (step.children .bank0).inputs .writeAddress =
        (step.children .control).outputs .o_writeAddress0 ∧
      (step.children .bank0).inputs .writeValue =
        (bif (step.children .control).outputs .o_writeSwap then
          (fun lane => step.inputs .i_data (upperLane configuration lane))
        else
          (fun lane => step.inputs .i_data (lowerLane configuration lane))) ∧
      (step.children .bank0).inputs (.readAddress 0) =
        (step.children .control).outputs .o_readAddress := by
  have trueRealizes := ModuleStructure.child_realizes satisfies .trueSource
  have splitSolution := ModuleStructure.child_isSolution satisfies .inputSplit
  have lowerSolution := ModuleStructure.child_isSolution satisfies .lowerCombine
  have upperSolution := ModuleStructure.child_isSolution satisfies .upperCombine
  have muxRealizes := ModuleStructure.child_realizes satisfies .bank0Write
  simp only [FinalReorder.structuralChildren] at trueRealizes
  simp only [FinalReorder.structuralChildren] at splitSolution
  simp only [FinalReorder.structuralChildren] at lowerSolution
  simp only [FinalReorder.structuralChildren] at upperSolution
  simp only [FinalReorder.structuralChildren] at muxRealizes
  obtain ⟨_, _, trueAllowed⟩ := Constant.allowed_of_realization .bit true
    trueRealizes
  have trueValue := Constant.output_of_allowed .bit true trueAllowed
  have splitValue := ModuleStructure.splitter_outputs_of_solution splitSolution
  have lowerValue := ModuleStructure.combiner_outputs_of_solution lowerSolution
  have upperValue := ModuleStructure.combiner_outputs_of_solution upperSolution
  have muxValue := Mux.result_of_realization (halfVectorType configuration)
    muxRealizes
  have trueInput := ModuleStructure.child_input satisfies .bank0 .writeEnable
  have addressInput := ModuleStructure.child_input satisfies .bank0 .writeAddress
  have valueInput := ModuleStructure.child_input satisfies .bank0 .writeValue
  have readInput := ModuleStructure.child_input satisfies .bank0 (.readAddress 0)
  have splitInput := ModuleStructure.child_input satisfies .inputSplit .value
  have muxSelect := ModuleStructure.child_input satisfies .bank0Write .select
  have muxFalse := ModuleStructure.child_input satisfies .bank0Write .whenFalse
  have muxTrue := ModuleStructure.child_input satisfies .bank0Write .whenTrue
  change (step.children .bank0).inputs .writeEnable =
    (step.children .trueSource).outputs .output at trueInput
  change (step.children .bank0).inputs .writeAddress =
    (step.children .control).outputs .o_writeAddress0 at addressInput
  change (step.children .bank0).inputs .writeValue =
    (step.children .bank0Write).outputs .result at valueInput
  change (step.children .bank0).inputs (.readAddress 0) =
    (step.children .control).outputs .o_readAddress at readInput
  change (step.children .trueSource).outputs .output = true at trueValue
  change (step.children .inputSplit).inputs .value = step.inputs .i_data at splitInput
  change (step.children .bank0Write).inputs .select =
    (step.children .control).outputs .o_writeSwap at muxSelect
  change (step.children .bank0Write).inputs .whenFalse =
    (step.children .lowerCombine).outputs .value at muxFalse
  change (step.children .bank0Write).inputs .whenTrue =
    (step.children .upperCombine).outputs .value at muxTrue
  change (step.children .bank0Write).outputs .result = bif
    (step.children .bank0Write).inputs .select then
      (step.children .bank0Write).inputs .whenTrue
    else (step.children .bank0Write).inputs .whenFalse at muxValue
  refine ⟨?_, addressInput, ?_, readInput⟩
  · rw [trueInput, trueValue]
  · rw [valueInput, muxValue, muxSelect, muxFalse, muxTrue]
    have lowerEqual : (step.children .lowerCombine).outputs .value =
        fun lane => step.inputs .i_data (lowerLane configuration lane) := by
      funext lane
      have combineAt := congrFun (congrFun lowerValue .value) lane
      have combineInput := ModuleStructure.child_input satisfies
        .lowerCombine lane
      have splitAt := congrFun splitValue (lowerLane configuration lane)
      change (step.children .lowerCombine).outputs .value lane =
        (step.children .lowerCombine).inputs lane at combineAt
      change (step.children .inputSplit).outputs
        (lowerLane configuration lane) =
          (step.children .inputSplit).inputs .value
            (lowerLane configuration lane) at splitAt
      change (step.children .lowerCombine).inputs lane =
        (step.children .inputSplit).outputs
          (lowerLane configuration lane) at combineInput
      rw [combineAt, combineInput, splitAt, splitInput]
    have upperEqual : (step.children .upperCombine).outputs .value =
        fun lane => step.inputs .i_data (upperLane configuration lane) := by
      funext lane
      have combineAt := congrFun (congrFun upperValue .value) lane
      have combineInput := ModuleStructure.child_input satisfies
        .upperCombine lane
      have splitAt := congrFun splitValue (upperLane configuration lane)
      change (step.children .upperCombine).outputs .value lane =
        (step.children .upperCombine).inputs lane at combineAt
      change (step.children .inputSplit).outputs
        (upperLane configuration lane) =
          (step.children .inputSplit).inputs .value
            (upperLane configuration lane) at splitAt
      change (step.children .upperCombine).inputs lane =
        (step.children .inputSplit).outputs
          (upperLane configuration lane) at combineInput
      rw [combineAt, combineInput, splitAt, splitInput]
    rw [lowerEqual, upperEqual]
    rfl

theorem bank1Inputs_of_solution
    {step : HierStep (reorderStructure depth configuration)}
    (satisfies : (reorderStructure depth configuration).IsSolution step) :
    (step.children .bank1).inputs .writeEnable = true ∧
      (step.children .bank1).inputs .writeAddress =
        (step.children .control).outputs .o_writeAddress1 ∧
      (step.children .bank1).inputs .writeValue =
        (bif (step.children .control).outputs .o_writeSwap then
          (fun lane => step.inputs .i_data (lowerLane configuration lane))
        else
          (fun lane => step.inputs .i_data (upperLane configuration lane))) ∧
      (step.children .bank1).inputs (.readAddress 0) =
        (step.children .control).outputs .o_readAddress := by
  have trueRealizes := ModuleStructure.child_realizes satisfies .trueSource
  have muxRealizes := ModuleStructure.child_realizes satisfies .bank1Write
  have lowerSolution := ModuleStructure.child_isSolution satisfies .lowerCombine
  have upperSolution := ModuleStructure.child_isSolution satisfies .upperCombine
  simp only [FinalReorder.structuralChildren] at muxRealizes
  simp only [FinalReorder.structuralChildren] at lowerSolution
  simp only [FinalReorder.structuralChildren] at upperSolution
  simp only [FinalReorder.structuralChildren] at trueRealizes
  obtain ⟨_, _, trueAllowed⟩ := Constant.allowed_of_realization .bit true
    trueRealizes
  have trueValue := Constant.output_of_allowed .bit true trueAllowed
  have lowerValue := ModuleStructure.combiner_outputs_of_solution lowerSolution
  have upperValue := ModuleStructure.combiner_outputs_of_solution upperSolution
  have muxValue := Mux.result_of_realization (halfVectorType configuration)
    muxRealizes
  have trueInput := ModuleStructure.child_input satisfies .bank1 .writeEnable
  have addressInput := ModuleStructure.child_input satisfies .bank1 .writeAddress
  have valueInput := ModuleStructure.child_input satisfies .bank1 .writeValue
  have readInput := ModuleStructure.child_input satisfies .bank1 (.readAddress 0)
  have muxSelect := ModuleStructure.child_input satisfies .bank1Write .select
  have muxFalse := ModuleStructure.child_input satisfies .bank1Write .whenFalse
  have muxTrue := ModuleStructure.child_input satisfies .bank1Write .whenTrue
  have splitSolution := ModuleStructure.child_isSolution satisfies .inputSplit
  simp only [FinalReorder.structuralChildren] at splitSolution
  have splitValue := ModuleStructure.splitter_outputs_of_solution splitSolution
  have splitInput := ModuleStructure.child_input satisfies .inputSplit .value
  change (step.children .bank1).inputs .writeEnable =
    (step.children .trueSource).outputs .output at trueInput
  change (step.children .bank1).inputs .writeAddress =
    (step.children .control).outputs .o_writeAddress1 at addressInput
  change (step.children .bank1).inputs .writeValue =
    (step.children .bank1Write).outputs .result at valueInput
  change (step.children .bank1).inputs (.readAddress 0) =
    (step.children .control).outputs .o_readAddress at readInput
  change (step.children .trueSource).outputs .output = true at trueValue
  change (step.children .inputSplit).inputs .value = step.inputs .i_data at splitInput
  change (step.children .bank1Write).inputs .select =
    (step.children .control).outputs .o_writeSwap at muxSelect
  change (step.children .bank1Write).inputs .whenFalse =
    (step.children .upperCombine).outputs .value at muxFalse
  change (step.children .bank1Write).inputs .whenTrue =
    (step.children .lowerCombine).outputs .value at muxTrue
  change (step.children .bank1Write).outputs .result = bif
    (step.children .bank1Write).inputs .select then
      (step.children .bank1Write).inputs .whenTrue
    else (step.children .bank1Write).inputs .whenFalse at muxValue
  refine ⟨?_, addressInput, ?_, readInput⟩
  · rw [trueInput, trueValue]
  · rw [valueInput, muxValue, muxSelect, muxFalse, muxTrue]
    have lowerEqual : (step.children .lowerCombine).outputs .value =
        fun lane => step.inputs .i_data (lowerLane configuration lane) := by
      funext lane
      have combineAt := congrFun (congrFun lowerValue .value) lane
      have combineInput := ModuleStructure.child_input satisfies
        .lowerCombine lane
      have splitAt := congrFun splitValue (lowerLane configuration lane)
      change (step.children .lowerCombine).outputs .value lane =
        (step.children .lowerCombine).inputs lane at combineAt
      change (step.children .inputSplit).outputs
        (lowerLane configuration lane) =
          (step.children .inputSplit).inputs .value
            (lowerLane configuration lane) at splitAt
      change (step.children .lowerCombine).inputs lane =
        (step.children .inputSplit).outputs
          (lowerLane configuration lane) at combineInput
      rw [combineAt, combineInput, splitAt, splitInput]
    have upperEqual : (step.children .upperCombine).outputs .value =
        fun lane => step.inputs .i_data (upperLane configuration lane) := by
      funext lane
      have combineAt := congrFun (congrFun upperValue .value) lane
      have combineInput := ModuleStructure.child_input satisfies
        .upperCombine lane
      have splitAt := congrFun splitValue (upperLane configuration lane)
      change (step.children .upperCombine).outputs .value lane =
        (step.children .upperCombine).inputs lane at combineAt
      change (step.children .inputSplit).outputs
        (upperLane configuration lane) =
          (step.children .inputSplit).inputs .value
            (upperLane configuration lane) at splitAt
      change (step.children .upperCombine).inputs lane =
        (step.children .inputSplit).outputs
          (upperLane configuration lane) at combineInput
      rw [combineAt, combineInput, splitAt, splitInput]
    rw [lowerEqual, upperEqual]
    rfl

theorem outputHalves_of_solution
    {step : HierStep (reorderStructure depth configuration)}
    (satisfies : (reorderStructure depth configuration).IsSolution step) :
    (∀ lane : Fin (halfLaneCount configuration),
      step.outputs .o_data (lowerLane configuration lane) =
        bif (step.children .control).outputs .o_readSwap then
          (bif (step.children .control).outputs .o_bypass then
            (step.children .bank1Write).outputs .result lane
          else (step.children .bank1).outputs (.readValue 0) lane)
        else (step.children .bank0).outputs (.readValue 0) lane) ∧
      (∀ lane : Fin (halfLaneCount configuration),
      step.outputs .o_data (upperLane configuration lane) =
        bif (step.children .control).outputs .o_readSwap then
          (step.children .bank0).outputs (.readValue 0) lane
        else
          (bif (step.children .control).outputs .o_bypass then
            (step.children .bank1Write).outputs .result lane
          else (step.children .bank1).outputs (.readValue 0) lane)) := by
  have bypassRealizes := ModuleStructure.child_realizes satisfies .bank1Bypass
  have lowerRealizes := ModuleStructure.child_realizes satisfies .lowerOutput
  have upperRealizes := ModuleStructure.child_realizes satisfies .upperOutput
  have lowerSplitSolution := ModuleStructure.child_isSolution satisfies .lowerSplit
  have upperSplitSolution := ModuleStructure.child_isSolution satisfies .upperSplit
  have combineSolution := ModuleStructure.child_isSolution satisfies .outputCombine
  simp only [FinalReorder.structuralChildren] at bypassRealizes
  simp only [FinalReorder.structuralChildren] at lowerRealizes
  simp only [FinalReorder.structuralChildren] at upperRealizes
  simp only [FinalReorder.structuralChildren] at lowerSplitSolution
  simp only [FinalReorder.structuralChildren] at upperSplitSolution
  simp only [FinalReorder.structuralChildren] at combineSolution
  have bypassValue := Mux.result_of_realization (halfVectorType configuration)
    bypassRealizes
  have lowerValue := Mux.result_of_realization (halfVectorType configuration)
    lowerRealizes
  have upperValue := Mux.result_of_realization (halfVectorType configuration)
    upperRealizes
  have lowerSplit := ModuleStructure.splitter_outputs_of_solution
    lowerSplitSolution
  have upperSplit := ModuleStructure.splitter_outputs_of_solution
    upperSplitSolution
  have combineValue := ModuleStructure.combiner_outputs_of_solution combineSolution
  have parentOutput := ModuleStructure.parent_output satisfies .o_data
  have bypassSelect := ModuleStructure.child_input satisfies .bank1Bypass .select
  have bypassFalse := ModuleStructure.child_input satisfies .bank1Bypass .whenFalse
  have bypassTrue := ModuleStructure.child_input satisfies .bank1Bypass .whenTrue
  have lowerSelect := ModuleStructure.child_input satisfies .lowerOutput .select
  have lowerFalse := ModuleStructure.child_input satisfies .lowerOutput .whenFalse
  have lowerTrue := ModuleStructure.child_input satisfies .lowerOutput .whenTrue
  have upperSelect := ModuleStructure.child_input satisfies .upperOutput .select
  have upperFalse := ModuleStructure.child_input satisfies .upperOutput .whenFalse
  have upperTrue := ModuleStructure.child_input satisfies .upperOutput .whenTrue
  have lowerSplitInput := ModuleStructure.child_input satisfies .lowerSplit .value
  have upperSplitInput := ModuleStructure.child_input satisfies .upperSplit .value
  change (step.children .bank1Bypass).outputs .result = bif
    (step.children .bank1Bypass).inputs .select then
      (step.children .bank1Bypass).inputs .whenTrue
    else (step.children .bank1Bypass).inputs .whenFalse at bypassValue
  change (step.children .lowerOutput).outputs .result = bif
    (step.children .lowerOutput).inputs .select then
      (step.children .lowerOutput).inputs .whenTrue
    else (step.children .lowerOutput).inputs .whenFalse at lowerValue
  change (step.children .upperOutput).outputs .result = bif
    (step.children .upperOutput).inputs .select then
      (step.children .upperOutput).inputs .whenTrue
    else (step.children .upperOutput).inputs .whenFalse at upperValue
  change step.outputs .o_data =
    (step.children .outputCombine).outputs .value at parentOutput
  change (step.children .bank1Bypass).inputs .select =
    (step.children .control).outputs .o_bypass at bypassSelect
  change (step.children .bank1Bypass).inputs .whenFalse =
    (step.children .bank1).outputs (.readValue 0) at bypassFalse
  change (step.children .bank1Bypass).inputs .whenTrue =
    (step.children .bank1Write).outputs .result at bypassTrue
  change (step.children .lowerOutput).inputs .select =
    (step.children .control).outputs .o_readSwap at lowerSelect
  change (step.children .lowerOutput).inputs .whenFalse =
    (step.children .bank0).outputs (.readValue 0) at lowerFalse
  change (step.children .lowerOutput).inputs .whenTrue =
    (step.children .bank1Bypass).outputs .result at lowerTrue
  change (step.children .upperOutput).inputs .select =
    (step.children .control).outputs .o_readSwap at upperSelect
  change (step.children .upperOutput).inputs .whenFalse =
    (step.children .bank1Bypass).outputs .result at upperFalse
  change (step.children .upperOutput).inputs .whenTrue =
    (step.children .bank0).outputs (.readValue 0) at upperTrue
  change (step.children .lowerSplit).inputs .value =
    (step.children .lowerOutput).outputs .result at lowerSplitInput
  change (step.children .upperSplit).inputs .value =
    (step.children .upperOutput).outputs .result at upperSplitInput
  constructor <;> intro lane
  · rw [parentOutput]
    have combineAt := congrFun (congrFun combineValue .value)
      (lowerLane configuration lane)
    change (step.children .outputCombine).outputs .value
      (lowerLane configuration lane) =
        (step.children .outputCombine).inputs
          (lowerLane configuration lane) at combineAt
    have combineInput := ModuleStructure.child_input satisfies
      .outputCombine (lowerLane configuration lane)
    simp only [FinalReorder.wiring, lowerLane] at combineInput
    simp only [dif_pos lane.isLt, EndpointContext.instanceOutput_value]
      at combineInput
    have combineInput' : (step.children .outputCombine).inputs
        (lowerLane configuration lane) =
          (step.children .lowerSplit).outputs lane := by
      simpa only [lowerLane] using combineInput
    rw [combineAt, combineInput']
    have splitAt := congrFun lowerSplit lane
    change (step.children .lowerSplit).outputs lane =
      (step.children .lowerSplit).inputs .value lane at splitAt
    rw [splitAt, lowerSplitInput, lowerValue, lowerSelect, lowerFalse,
      lowerTrue, bypassValue, bypassSelect, bypassFalse, bypassTrue]
    cases (step.children .control).outputs .o_readSwap <;>
      cases (step.children .control).outputs .o_bypass <;> rfl
  · rw [parentOutput]
    have combineAt := congrFun (congrFun combineValue .value)
      (upperLane configuration lane)
    change (step.children .outputCombine).outputs .value
      (upperLane configuration lane) =
        (step.children .outputCombine).inputs
          (upperLane configuration lane) at combineAt
    have combineInput := ModuleStructure.child_input satisfies
      .outputCombine (upperLane configuration lane)
    have notLower : ¬ (upperLane configuration lane).val <
        halfLaneCount configuration := by
      simp [upperLane]
    simp only [FinalReorder.wiring, notLower, dite_false,
      EndpointContext.instanceOutput_value]
      at combineInput
    have indexEqual : (upperLane configuration lane).val -
        halfLaneCount configuration = lane.val := by
      simp [upperLane]
    let indexedLane : Fin (halfLaneCount configuration) :=
      ⟨(upperLane configuration lane).val - halfLaneCount configuration, by
        have bound := (upperLane configuration lane).isLt
        have full := two_mul_halfLaneCount configuration
        omega⟩
    have indexedLaneEqual : indexedLane = lane := by
      apply Fin.ext
      dsimp only [indexedLane]
      exact indexEqual
    have combineInput' : (step.children .outputCombine).inputs
        (upperLane configuration lane) =
          (step.children .upperSplit).outputs lane := by
      calc
        _ = (step.children .upperSplit).outputs indexedLane := by
          simpa only [indexedLane] using combineInput
        _ = _ := by rw [indexedLaneEqual]
    rw [combineAt, combineInput']
    have splitAt := congrFun upperSplit lane
    change (step.children .upperSplit).outputs lane =
      (step.children .upperSplit).inputs .value lane at splitAt
    rw [splitAt, upperSplitInput, upperValue, upperSelect, upperFalse,
      upperTrue, bypassValue, bypassSelect, bypassFalse, bypassTrue]
    cases (step.children .control).outputs .o_readSwap <;>
      cases (step.children .control).outputs .o_bypass <;> rfl

end HTFFT.Silean.FinalReorder.Internal
