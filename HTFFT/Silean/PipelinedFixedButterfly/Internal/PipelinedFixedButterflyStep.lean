import HTFFT.Silean.PipelinedFixedButterfly.Internal.PipelinedFixedButterflyArithmetic
import HTFFT.Silean.PipelinedFixedButterfly.Internal.PipelinedFixedButterflyStructural

/-! One-cycle structural consequences used by the butterfly trace proof. -/

namespace HTFFT.Silean.PipelinedFixedButterfly.Internal

open _root_.Silean
open _root_.Silean.Modules
open HTFFT.FixedPoint

private abbrev structureFor
    (dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits : Nat)
    (registerInputs : Bool) (multiplierLatency : Nat)
    (registerBeforeRounding registerProduct registerOutputs : Bool) :=
  moduleStructure dataWidth dataFractionalBits twiddleWidth
    twiddleFractionalBits registerInputs multiplierLatency
    registerBeforeRounding registerProduct registerOutputs

/-- The complex multiplier sees the high real and low imaginary halves of the
registered `b` and twiddle values. -/
theorem productInputs_of_solution
    (dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits : Nat)
    (registerInputs : Bool) (multiplierLatency : Nat)
    (registerBeforeRounding registerProduct registerOutputs : Bool)
    {hierStep : HierStep
      (structureFor dataWidth dataFractionalBits twiddleWidth
        twiddleFractionalBits registerInputs multiplierLatency
        registerBeforeRounding registerProduct registerOutputs)}
    (satisfies :
      (structureFor dataWidth dataFractionalBits twiddleWidth
        twiddleFractionalBits registerInputs multiplierLatency
        registerBeforeRounding registerProduct registerOutputs).IsSolution
          hierStep) :
    (hierStep.children .product).inputs .leftReal =
        highComponent dataWidth
          ((hierStep.children .bInputDelay).outputs .output) ∧
      (hierStep.children .product).inputs .leftImag =
        lowComponent dataWidth
          ((hierStep.children .bInputDelay).outputs .output) ∧
      (hierStep.children .product).inputs .rightReal =
        highComponent twiddleWidth
          ((hierStep.children .twiddleInputDelay).outputs .output) ∧
      (hierStep.children .product).inputs .rightImag =
        lowComponent twiddleWidth
          ((hierStep.children .twiddleInputDelay).outputs .output) := by
  have bRealizes := ModuleStructure.child_realizes satisfies (.bSplit)
  have twiddleRealizes :=
    ModuleStructure.child_realizes satisfies (.twiddleSplit)
  simp only [structuralChildren] at bRealizes twiddleRealizes
  have bParts := VectorSplit.outputs_of_realization
    .bit dataWidth dataWidth bRealizes
  have twiddleParts := VectorSplit.outputs_of_realization
    .bit twiddleWidth twiddleWidth twiddleRealizes
  change (hierStep.children .bSplit).outputs .left =
      VectorSplit.leftPart ((hierStep.children .bSplit).inputs .value) ∧
    (hierStep.children .bSplit).outputs .right =
      VectorSplit.rightPart ((hierStep.children .bSplit).inputs .value)
    at bParts
  change (hierStep.children .twiddleSplit).outputs .left =
      VectorSplit.leftPart ((hierStep.children .twiddleSplit).inputs .value) ∧
    (hierStep.children .twiddleSplit).outputs .right =
      VectorSplit.rightPart ((hierStep.children .twiddleSplit).inputs .value)
    at twiddleParts
  have bInput := ModuleStructure.child_input satisfies (.bSplit) (.value)
  have twiddleInput :=
    ModuleStructure.child_input satisfies (.twiddleSplit) (.value)
  change (hierStep.children .bSplit).inputs .value =
    (hierStep.children .bInputDelay).outputs .output at bInput
  change (hierStep.children .twiddleSplit).inputs .value =
    (hierStep.children .twiddleInputDelay).outputs .output at twiddleInput
  rw [bInput] at bParts
  rw [twiddleInput] at twiddleParts
  have leftReal :=
    ModuleStructure.child_input satisfies (.product) (.leftReal)
  have leftImag :=
    ModuleStructure.child_input satisfies (.product) (.leftImag)
  have rightReal :=
    ModuleStructure.child_input satisfies (.product) (.rightReal)
  have rightImag :=
    ModuleStructure.child_input satisfies (.product) (.rightImag)
  change (hierStep.children .product).inputs .leftReal =
    (hierStep.children .bSplit).outputs .right at leftReal
  change (hierStep.children .product).inputs .leftImag =
    (hierStep.children .bSplit).outputs .left at leftImag
  change (hierStep.children .product).inputs .rightReal =
    (hierStep.children .twiddleSplit).outputs .right at rightReal
  change (hierStep.children .product).inputs .rightImag =
    (hierStep.children .twiddleSplit).outputs .left at rightImag
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [leftReal, bParts.2]
    rfl
  · rw [leftImag, bParts.1]
    rfl
  · rw [rightReal, twiddleParts.2]
    rfl
  · rw [rightImag, twiddleParts.1]
    rfl

/-- The optional product register receives the rounded multiplier result after
the explicit data-width boundary and complex packing. -/
theorem productDelayInput_of_solution
    (dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits : Nat)
    (registerInputs : Bool) (multiplierLatency : Nat)
    (registerBeforeRounding registerProduct registerOutputs : Bool)
    {hierStep : HierStep
      (structureFor dataWidth dataFractionalBits twiddleWidth
        twiddleFractionalBits registerInputs multiplierLatency
        registerBeforeRounding registerProduct registerOutputs)}
    (satisfies :
      (structureFor dataWidth dataFractionalBits twiddleWidth
        twiddleFractionalBits registerInputs multiplierLatency
        registerBeforeRounding registerProduct registerOutputs).IsSolution
          hierStep) :
    (hierStep.children .productDelay).inputs .input =
      packProductOutputs
        ⟨dataWidth, dataFractionalBits⟩
        ⟨twiddleWidth, twiddleFractionalBits⟩
        ((hierStep.children .product).outputs .resultReal)
        ((hierStep.children .product).outputs .resultImag) := by
  have realRealizes :=
    ModuleStructure.child_realizes satisfies (.productRealNarrow)
  have imagRealizes :=
    ModuleStructure.child_realizes satisfies (.productImagNarrow)
  have combineRealizes :=
    ModuleStructure.child_realizes satisfies (.productCombine)
  simp only [structuralChildren] at realRealizes imagRealizes combineRealizes
  have realOutput := VectorLayout.output_of_realization
    (PipelinedSignedComplexMultiply.resultWidth dataWidth twiddleWidth
      twiddleFractionalBits)
    dataWidth
    (VectorLayout.extensionLayout true
      (PipelinedSignedComplexMultiply.resultWidth dataWidth twiddleWidth
        twiddleFractionalBits) dataWidth)
    realRealizes
  have imagOutput := VectorLayout.output_of_realization
    (PipelinedSignedComplexMultiply.resultWidth dataWidth twiddleWidth
      twiddleFractionalBits)
    dataWidth
    (VectorLayout.extensionLayout true
      (PipelinedSignedComplexMultiply.resultWidth dataWidth twiddleWidth
        twiddleFractionalBits) dataWidth)
    imagRealizes
  change (hierStep.children .productRealNarrow).outputs .output =
    VectorLayout.apply
      (VectorLayout.extensionLayout true
        (PipelinedSignedComplexMultiply.resultWidth dataWidth twiddleWidth
          twiddleFractionalBits) dataWidth)
      ((hierStep.children .productRealNarrow).inputs .input) at realOutput
  change (hierStep.children .productImagNarrow).outputs .output =
    VectorLayout.apply
      (VectorLayout.extensionLayout true
        (PipelinedSignedComplexMultiply.resultWidth dataWidth twiddleWidth
          twiddleFractionalBits) dataWidth)
      ((hierStep.children .productImagNarrow).inputs .input) at imagOutput
  have realInput :=
    ModuleStructure.child_input satisfies (.productRealNarrow) (.input)
  have imagInput :=
    ModuleStructure.child_input satisfies (.productImagNarrow) (.input)
  change (hierStep.children .productRealNarrow).inputs .input =
    (hierStep.children .product).outputs .resultReal at realInput
  change (hierStep.children .productImagNarrow).inputs .input =
    (hierStep.children .product).outputs .resultImag at imagInput
  rw [realInput] at realOutput
  rw [imagInput] at imagOutput
  have combined := VectorConcat.result_of_realization
    .bit dataWidth dataWidth combineRealizes
  change (hierStep.children .productCombine).outputs .result =
    VectorConcat.concat
      ((hierStep.children .productCombine).inputs .left)
      ((hierStep.children .productCombine).inputs .right) at combined
  have combineImag :=
    ModuleStructure.child_input satisfies (.productCombine) (.left)
  have combineReal :=
    ModuleStructure.child_input satisfies (.productCombine) (.right)
  change (hierStep.children .productCombine).inputs .left =
    (hierStep.children .productImagNarrow).outputs .output at combineImag
  change (hierStep.children .productCombine).inputs .right =
    (hierStep.children .productRealNarrow).outputs .output at combineReal
  rw [combineImag, imagOutput, combineReal, realOutput] at combined
  have delayInput :=
    ModuleStructure.child_input satisfies (.productDelay) (.input)
  change (hierStep.children .productDelay).inputs .input =
    (hierStep.children .productCombine).outputs .result at delayInput
  rw [delayInput, combined]
  rfl

/-- The alignment delay starts from the registered input `a`. -/
theorem aAlignInput_of_solution
    (dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits : Nat)
    (registerInputs : Bool) (multiplierLatency : Nat)
    (registerBeforeRounding registerProduct registerOutputs : Bool)
    {hierStep : HierStep
      (structureFor dataWidth dataFractionalBits twiddleWidth
        twiddleFractionalBits registerInputs multiplierLatency
        registerBeforeRounding registerProduct registerOutputs)}
    (satisfies :
      (structureFor dataWidth dataFractionalBits twiddleWidth
        twiddleFractionalBits registerInputs multiplierLatency
        registerBeforeRounding registerProduct registerOutputs).IsSolution
          hierStep) :
    (hierStep.children .aAlignDelay).inputs .input =
      (hierStep.children .aInputDelay).outputs .output := by
  exact ModuleStructure.child_input satisfies (.aAlignDelay) (.input)

/-- The two optional output registers receive the complete combinational
upper and lower butterfly values. -/
theorem outputDelayInputs_of_solution
    (dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits : Nat)
    (registerInputs : Bool) (multiplierLatency : Nat)
    (registerBeforeRounding registerProduct registerOutputs : Bool)
    {hierStep : HierStep
      (structureFor dataWidth dataFractionalBits twiddleWidth
        twiddleFractionalBits registerInputs multiplierLatency
        registerBeforeRounding registerProduct registerOutputs)}
    (satisfies :
      (structureFor dataWidth dataFractionalBits twiddleWidth
        twiddleFractionalBits registerInputs multiplierLatency
        registerBeforeRounding registerProduct registerOutputs).IsSolution
          hierStep) :
    (hierStep.children .upperOutputDelay).inputs .input =
        upperCircuitValue ⟨dataWidth, dataFractionalBits⟩
          ((hierStep.children .aAlignDelay).outputs .output)
          ((hierStep.children .productDelay).outputs .output) ∧
      (hierStep.children .lowerOutputDelay).inputs .input =
        lowerCircuitValue ⟨dataWidth, dataFractionalBits⟩
          ((hierStep.children .aAlignDelay).outputs .output)
          ((hierStep.children .productDelay).outputs .output) := by
  have aRealizes := ModuleStructure.child_realizes satisfies (.aSplit)
  have productRealizes :=
    ModuleStructure.child_realizes satisfies (.productSplit)
  simp only [structuralChildren] at aRealizes productRealizes
  have aParts := VectorSplit.outputs_of_realization
    .bit dataWidth dataWidth aRealizes
  have productParts := VectorSplit.outputs_of_realization
    .bit dataWidth dataWidth productRealizes
  change (hierStep.children .aSplit).outputs .left =
      VectorSplit.leftPart ((hierStep.children .aSplit).inputs .value) ∧
    (hierStep.children .aSplit).outputs .right =
      VectorSplit.rightPart ((hierStep.children .aSplit).inputs .value)
    at aParts
  change (hierStep.children .productSplit).outputs .left =
      VectorSplit.leftPart ((hierStep.children .productSplit).inputs .value) ∧
    (hierStep.children .productSplit).outputs .right =
      VectorSplit.rightPart ((hierStep.children .productSplit).inputs .value)
    at productParts
  have aInput := ModuleStructure.child_input satisfies (.aSplit) (.value)
  have productInput :=
    ModuleStructure.child_input satisfies (.productSplit) (.value)
  change (hierStep.children .aSplit).inputs .value =
    (hierStep.children .aAlignDelay).outputs .output at aInput
  change (hierStep.children .productSplit).inputs .value =
    (hierStep.children .productDelay).outputs .output at productInput
  rw [aInput] at aParts
  rw [productInput] at productParts

  have upperRealRealizes :=
    ModuleStructure.child_realizes satisfies (.upperReal)
  have upperImagRealizes :=
    ModuleStructure.child_realizes satisfies (.upperImag)
  have lowerRealRealizes :=
    ModuleStructure.child_realizes satisfies (.lowerReal)
  have lowerImagRealizes :=
    ModuleStructure.child_realizes satisfies (.lowerImag)
  simp only [structuralChildren] at upperRealRealizes upperImagRealizes lowerRealRealizes lowerImagRealizes
  have upperReal := Add.result_of_realization
    dataWidth dataWidth true true true upperRealRealizes
  have upperImag := Add.result_of_realization
    dataWidth dataWidth true true true upperImagRealizes
  have lowerReal := Sub.result_of_realization
    dataWidth dataWidth true true true lowerRealRealizes
  have lowerImag := Sub.result_of_realization
    dataWidth dataWidth true true true lowerImagRealizes
  change (hierStep.children .upperReal).outputs .result =
    Add.resultValue dataWidth dataWidth true true true
      ((hierStep.children .upperReal).inputs .left)
      ((hierStep.children .upperReal).inputs .right) at upperReal
  change (hierStep.children .upperImag).outputs .result =
    Add.resultValue dataWidth dataWidth true true true
      ((hierStep.children .upperImag).inputs .left)
      ((hierStep.children .upperImag).inputs .right) at upperImag
  change (hierStep.children .lowerReal).outputs .result =
    Sub.resultValue dataWidth dataWidth true true true
      ((hierStep.children .lowerReal).inputs .left)
      ((hierStep.children .lowerReal).inputs .right) at lowerReal
  change (hierStep.children .lowerImag).outputs .result =
    Sub.resultValue dataWidth dataWidth true true true
      ((hierStep.children .lowerImag).inputs .left)
      ((hierStep.children .lowerImag).inputs .right) at lowerImag

  have upperRealLeft :=
    ModuleStructure.child_input satisfies (.upperReal) (.left)
  have upperRealRight :=
    ModuleStructure.child_input satisfies (.upperReal) (.right)
  have upperImagLeft :=
    ModuleStructure.child_input satisfies (.upperImag) (.left)
  have upperImagRight :=
    ModuleStructure.child_input satisfies (.upperImag) (.right)
  have lowerRealLeft :=
    ModuleStructure.child_input satisfies (.lowerReal) (.left)
  have lowerRealRight :=
    ModuleStructure.child_input satisfies (.lowerReal) (.right)
  have lowerImagLeft :=
    ModuleStructure.child_input satisfies (.lowerImag) (.left)
  have lowerImagRight :=
    ModuleStructure.child_input satisfies (.lowerImag) (.right)
  change (hierStep.children .upperReal).inputs .left =
    (hierStep.children .aSplit).outputs .right at upperRealLeft
  change (hierStep.children .upperReal).inputs .right =
    (hierStep.children .productSplit).outputs .right at upperRealRight
  change (hierStep.children .upperImag).inputs .left =
    (hierStep.children .aSplit).outputs .left at upperImagLeft
  change (hierStep.children .upperImag).inputs .right =
    (hierStep.children .productSplit).outputs .left at upperImagRight
  change (hierStep.children .lowerReal).inputs .left =
    (hierStep.children .aSplit).outputs .right at lowerRealLeft
  change (hierStep.children .lowerReal).inputs .right =
    (hierStep.children .productSplit).outputs .right at lowerRealRight
  change (hierStep.children .lowerImag).inputs .left =
    (hierStep.children .aSplit).outputs .left at lowerImagLeft
  change (hierStep.children .lowerImag).inputs .right =
    (hierStep.children .productSplit).outputs .left at lowerImagRight
  rw [upperRealLeft, aParts.2, upperRealRight, productParts.2] at upperReal
  rw [upperImagLeft, aParts.1, upperImagRight, productParts.1] at upperImag
  rw [lowerRealLeft, aParts.2, lowerRealRight, productParts.2] at lowerReal
  rw [lowerImagLeft, aParts.1, lowerImagRight, productParts.1] at lowerImag

  have upperCombineRealizes :=
    ModuleStructure.child_realizes satisfies (.upperCombine)
  have lowerCombineRealizes :=
    ModuleStructure.child_realizes satisfies (.lowerCombine)
  simp only [structuralChildren] at upperCombineRealizes lowerCombineRealizes
  have upperCombined := VectorConcat.result_of_realization .bit
    (outputComponentWidth ⟨dataWidth, dataFractionalBits⟩)
    (outputComponentWidth ⟨dataWidth, dataFractionalBits⟩)
    upperCombineRealizes
  have lowerCombined := VectorConcat.result_of_realization .bit
    (outputComponentWidth ⟨dataWidth, dataFractionalBits⟩)
    (outputComponentWidth ⟨dataWidth, dataFractionalBits⟩)
    lowerCombineRealizes
  change (hierStep.children .upperCombine).outputs .result =
    VectorConcat.concat
      ((hierStep.children .upperCombine).inputs .left)
      ((hierStep.children .upperCombine).inputs .right) at upperCombined
  change (hierStep.children .lowerCombine).outputs .result =
    VectorConcat.concat
      ((hierStep.children .lowerCombine).inputs .left)
      ((hierStep.children .lowerCombine).inputs .right) at lowerCombined
  have upperCombineImag :=
    ModuleStructure.child_input satisfies (.upperCombine) (.left)
  have upperCombineReal :=
    ModuleStructure.child_input satisfies (.upperCombine) (.right)
  have lowerCombineImag :=
    ModuleStructure.child_input satisfies (.lowerCombine) (.left)
  have lowerCombineReal :=
    ModuleStructure.child_input satisfies (.lowerCombine) (.right)
  change (hierStep.children .upperCombine).inputs .left =
    (hierStep.children .upperImag).outputs .result at upperCombineImag
  change (hierStep.children .upperCombine).inputs .right =
    (hierStep.children .upperReal).outputs .result at upperCombineReal
  change (hierStep.children .lowerCombine).inputs .left =
    (hierStep.children .lowerImag).outputs .result at lowerCombineImag
  change (hierStep.children .lowerCombine).inputs .right =
    (hierStep.children .lowerReal).outputs .result at lowerCombineReal
  rw [upperCombineImag, upperImag, upperCombineReal, upperReal] at upperCombined
  rw [lowerCombineImag, lowerImag, lowerCombineReal, lowerReal] at lowerCombined
  have upperDelayInput :=
    ModuleStructure.child_input satisfies (.upperOutputDelay) (.input)
  have lowerDelayInput :=
    ModuleStructure.child_input satisfies (.lowerOutputDelay) (.input)
  change (hierStep.children .upperOutputDelay).inputs .input =
    (hierStep.children .upperCombine).outputs .result at upperDelayInput
  change (hierStep.children .lowerOutputDelay).inputs .input =
    (hierStep.children .lowerCombine).outputs .result at lowerDelayInput
  constructor
  · rw [upperDelayInput, upperCombined]
    rfl
  · rw [lowerDelayInput, lowerCombined]
    rfl

/-- Parent outputs are the two optional output-register results. -/
theorem parentOutputs_of_solution
    (dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits : Nat)
    (registerInputs : Bool) (multiplierLatency : Nat)
    (registerBeforeRounding registerProduct registerOutputs : Bool)
    {hierStep : HierStep
      (structureFor dataWidth dataFractionalBits twiddleWidth
        twiddleFractionalBits registerInputs multiplierLatency
        registerBeforeRounding registerProduct registerOutputs)}
    (satisfies :
      (structureFor dataWidth dataFractionalBits twiddleWidth
        twiddleFractionalBits registerInputs multiplierLatency
        registerBeforeRounding registerProduct registerOutputs).IsSolution
          hierStep) :
    hierStep.outputs .upper =
        (hierStep.children .upperOutputDelay).outputs .output ∧
      hierStep.outputs .lower =
        (hierStep.children .lowerOutputDelay).outputs .output := by
  exact ⟨ModuleStructure.parent_output satisfies (.upper),
    ModuleStructure.parent_output satisfies (.lower)⟩

end HTFFT.Silean.PipelinedFixedButterfly.Internal
