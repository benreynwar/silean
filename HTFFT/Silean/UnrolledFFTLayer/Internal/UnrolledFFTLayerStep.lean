import HTFFT.Silean.UnrolledFFTLayer.Internal.UnrolledFFTLayerStructural

/-! One-cycle structural equations used by the layer trace proof. -/

namespace HTFFT.Silean.UnrolledFFTLayer.Internal

open _root_.Silean
open _root_.Silean.Modules

variable {depth : Nat}
  {configuration : UnrolledFFT.Configuration depth}
  {table : HTFFT.Fixed.TwiddleTable depth}
  {stage : Fin depth}

/-- The aggregate splitter exposes exactly the corresponding parent input
sample. -/
theorem inputSample_of_solution
    {hierStep : HierStep (moduleStructure depth configuration table stage)}
    (satisfies :
      (moduleStructure depth configuration table stage).IsSolution hierStep)
    (sample : Fin (2 ^ depth)) :
    (hierStep.children .inputSplit).outputs sample =
      hierStep.inputs .input sample := by
  have splitInput := ModuleStructure.child_input satisfies
    (.inputSplit) (.value)
  change (hierStep.children .inputSplit).inputs .value =
    hierStep.inputs .input at splitInput
  have splitOutputs : (hierStep.children .inputSplit).outputs =
      (inputSplitter configuration stage).outputValues
        (hierStep.children .inputSplit).inputs := by
    exact ModuleStructure.splitter_outputs_of_solution
      (by simpa only [structuralChildren] using
        ModuleStructure.child_isSolution satisfies (.inputSplit))
  calc
    (hierStep.children .inputSplit).outputs sample =
        (inputSplitter configuration stage).outputValues
          (hierStep.children .inputSplit).inputs sample :=
      congrFun splitOutputs sample
    _ = (hierStep.children .inputSplit).inputs .value sample := rfl
    _ = hierStep.inputs .input sample := congrFun splitInput sample

/-- The recursive constant module produces the complete packed table selected
for this layer. -/
theorem twiddleTable_of_solution
    {hierStep : HierStep (moduleStructure depth configuration table stage)}
    (satisfies :
      (moduleStructure depth configuration table stage).IsSolution hierStep) :
    (hierStep.children .twiddleTable).outputs .output =
      twiddleValues configuration table stage := by
  have realizes := ModuleStructure.child_realizes satisfies (.twiddleTable)
  simp only [structuralChildren] at realizes
  obtain ⟨_, _, allowed⟩ := Constant.allowed_of_realization
    (twiddleTableType configuration stage)
    (twiddleValues configuration table stage) realizes
  exact Constant.output_of_allowed
    (twiddleTableType configuration stage)
    (twiddleValues configuration table stage) allowed

/-- The table splitter exposes the encoded twiddle at the selected offset. -/
theorem twiddleAt_of_solution
    {hierStep : HierStep (moduleStructure depth configuration table stage)}
    (satisfies :
      (moduleStructure depth configuration table stage).IsSolution hierStep)
    (offset : Fin (2 ^ stage.val)) :
    (hierStep.children .twiddleSplit).outputs offset =
      twiddleValues configuration table stage offset := by
  have splitInput := ModuleStructure.child_input satisfies
    (.twiddleSplit) (.value)
  change (hierStep.children .twiddleSplit).inputs .value =
    (hierStep.children .twiddleTable).outputs .output at splitInput
  have splitOutputs : (hierStep.children .twiddleSplit).outputs =
      (twiddleSplitter configuration stage).outputValues
        (hierStep.children .twiddleSplit).inputs := by
    exact ModuleStructure.splitter_outputs_of_solution
      (by simpa only [structuralChildren] using
        ModuleStructure.child_isSolution satisfies (.twiddleSplit))
  calc
    (hierStep.children .twiddleSplit).outputs offset =
        (twiddleSplitter configuration stage).outputValues
          (hierStep.children .twiddleSplit).inputs offset :=
      congrFun splitOutputs offset
    _ = (hierStep.children .twiddleSplit).inputs .value offset := rfl
    _ = (hierStep.children .twiddleTable).outputs .output offset := by
      rw [splitInput]
    _ = twiddleValues configuration table stage offset := by
      rw [twiddleTable_of_solution satisfies]

/-- All three inputs of one butterfly child are the corresponding parent
samples and static table entry. -/
theorem butterflyInputs_of_solution
    {hierStep : HierStep (moduleStructure depth configuration table stage)}
    (satisfies :
      (moduleStructure depth configuration table stage).IsSolution hierStep)
    (index : ButterflyIndex depth stage) :
    (hierStep.children (.butterfly index)).inputs .a =
        hierStep.inputs .input (sampleIndex index 0) ∧
      (hierStep.children (.butterfly index)).inputs .b =
        hierStep.inputs .input (sampleIndex index 1) ∧
      (hierStep.children (.butterfly index)).inputs .twiddle =
        twiddleValues configuration table stage index.2 := by
  have aInput := ModuleStructure.child_input satisfies
    (.butterfly index) (.a)
  have bInput := ModuleStructure.child_input satisfies
    (.butterfly index) (.b)
  have twiddleInput := ModuleStructure.child_input satisfies
    (.butterfly index) (.twiddle)
  change (hierStep.children (.butterfly index)).inputs .a =
    (hierStep.children .inputSplit).outputs (sampleIndex index 0) at aInput
  change (hierStep.children (.butterfly index)).inputs .b =
    (hierStep.children .inputSplit).outputs (sampleIndex index 1) at bInput
  change (hierStep.children (.butterfly index)).inputs .twiddle =
    (hierStep.children .twiddleSplit).outputs index.2 at twiddleInput
  exact ⟨aInput.trans (inputSample_of_solution satisfies _),
    bInput.trans (inputSample_of_solution satisfies _),
    twiddleInput.trans (twiddleAt_of_solution satisfies _)⟩

/-- The parent output sample is the appropriately transported upper or lower
output of its owning butterfly. -/
theorem outputSample_of_solution
    {hierStep : HierStep (moduleStructure depth configuration table stage)}
    (satisfies :
      (moduleStructure depth configuration table stage).IsSolution hierStep)
    (sample : Fin (2 ^ depth)) :
    hierStep.outputs .output sample =
      let index := butterflyIndexOfSample (stage := stage) sample
      let branch := branchOfSample stage sample
      if branch = 0 then
        castButterflyOutput configuration stage
          ((hierStep.children (.butterfly index)).outputs .upper)
      else
        castButterflyOutput configuration stage
          ((hierStep.children (.butterfly index)).outputs .lower) := by
  have parentOutput := ModuleStructure.parent_output satisfies (.output)
  change hierStep.outputs .output =
    (hierStep.children .outputCombine).outputs .value at parentOutput
  have combineOutputs : (hierStep.children .outputCombine).outputs =
      (outputCombiner configuration stage).outputValues
        (hierStep.children .outputCombine).inputs := by
    exact ModuleStructure.combiner_outputs_of_solution
      (by simpa only [structuralChildren] using
        ModuleStructure.child_isSolution satisfies (.outputCombine))
  have combineAt : (hierStep.children .outputCombine).outputs .value sample =
      (hierStep.children .outputCombine).inputs sample := by
    exact congrFun (congrFun combineOutputs (.value)) sample
  have combineInput := ModuleStructure.child_input satisfies
    (.outputCombine) sample
  by_cases upper : branchOfSample stage sample = 0
  · simp only [wiring, upper, if_true, SignalSource.value_castType,
      EndpointContext.instanceOutput_value] at combineInput
    rw [castTypeValue_eq_castButterflyOutput] at combineInput
    change (hierStep.children .outputCombine).inputs sample =
      castButterflyOutput configuration stage
        ((hierStep.children (.butterfly
          (butterflyIndexOfSample (stage := stage) sample))).outputs .upper)
      at combineInput
    rw [parentOutput, combineAt, combineInput]
    simp [upper]
  · simp only [wiring, upper, if_false, SignalSource.value_castType,
      EndpointContext.instanceOutput_value] at combineInput
    rw [castTypeValue_eq_castButterflyOutput] at combineInput
    change (hierStep.children .outputCombine).inputs sample =
      castButterflyOutput configuration stage
        ((hierStep.children (.butterfly
          (butterflyIndexOfSample (stage := stage) sample))).outputs .lower)
      at combineInput
    rw [parentOutput, combineAt, combineInput]
    simp [upper]

end HTFFT.Silean.UnrolledFFTLayer.Internal
