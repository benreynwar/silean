import HTFFT.Silean.FFTStageLane.FFTStageLaneContract
import HTFFT.Silean.FFTStageLane.Internal.FFTStageLaneStructural

/-! One-cycle structural equations for a rolled-stage lane. -/

namespace HTFFT.Silean.FFTStageLane.Internal

open _root_.Silean
open _root_.Silean.Modules
open HTFFT.FixedPoint

variable {dataFormat twiddleFormat : Format}
  {pairExponent phaseWidth laneAddressWidth lane : Nat}
  {twiddleDefinitionName : String}
  {twiddleValues : Fin (ROM.entryCount (laneAddressWidth + phaseWidth)) →
    (FFTStageLane.twiddleSignalType twiddleFormat).Denote}
  {pipeline : PipelinedFixedButterfly.Pipeline}

private abbrev laneStructure (dataFormat twiddleFormat : Format)
    (pairExponent phaseWidth laneAddressWidth lane : Nat)
    (twiddleDefinitionName : String)
    (twiddleValues : Fin (ROM.entryCount (laneAddressWidth + phaseWidth)) →
      (FFTStageLane.twiddleSignalType twiddleFormat).Denote)
    (pipeline : PipelinedFixedButterfly.Pipeline) :=
  moduleStructure dataFormat twiddleFormat pairExponent phaseWidth
    laneAddressWidth lane twiddleDefinitionName twiddleValues pipeline

theorem firstDelayInput_of_solution
    {hierStep : HierStep (laneStructure dataFormat twiddleFormat pairExponent
      phaseWidth laneAddressWidth lane twiddleDefinitionName twiddleValues
      pipeline)}
    (satisfies : (laneStructure dataFormat twiddleFormat pairExponent
      phaseWidth laneAddressWidth lane twiddleDefinitionName twiddleValues
      pipeline).IsSolution hierStep) :
    (hierStep.children .firstDelay).inputs .input =
      FFTStageLane.firstDelayInput dataFormat twiddleFormat phaseWidth
        hierStep.inputs := by
  have delayInput := ModuleStructure.child_input satisfies .firstDelay .input
  have muxRealizes := ModuleStructure.child_realizes satisfies .firstInputMux
  simp only [structuralChildren] at muxRealizes
  have muxResult := Mux.result_of_realization
    (FFTStageLane.dataSignalType dataFormat) muxRealizes
  change (hierStep.children .firstInputMux).outputs .result =
    bif (hierStep.children .firstInputMux).inputs .select then
      (hierStep.children .firstInputMux).inputs .whenTrue
    else (hierStep.children .firstInputMux).inputs .whenFalse at muxResult
  have select := ModuleStructure.child_input satisfies .firstInputMux .select
  have whenFalse := ModuleStructure.child_input satisfies
    .firstInputMux .whenFalse
  have whenTrue := ModuleStructure.child_input satisfies
    .firstInputMux .whenTrue
  change (hierStep.children .firstDelay).inputs .input =
    (hierStep.children .firstInputMux).outputs .result at delayInput
  change (hierStep.children .firstInputMux).inputs .select =
    hierStep.inputs .i_firstHalf at select
  change (hierStep.children .firstInputMux).inputs .whenFalse =
    hierStep.inputs .i_branchB at whenFalse
  change (hierStep.children .firstInputMux).inputs .whenTrue =
    hierStep.inputs .i_branchA at whenTrue
  rw [delayInput, muxResult, select, whenFalse, whenTrue]
  rfl

theorem secondDelayInput_of_solution
    {hierStep : HierStep (laneStructure dataFormat twiddleFormat pairExponent
      phaseWidth laneAddressWidth lane twiddleDefinitionName twiddleValues
      pipeline)}
    (satisfies : (laneStructure dataFormat twiddleFormat pairExponent
      phaseWidth laneAddressWidth lane twiddleDefinitionName twiddleValues
      pipeline).IsSolution hierStep) :
    (hierStep.children .secondDelay).inputs .input =
      FFTStageLane.secondDelayInput dataFormat twiddleFormat phaseWidth
        hierStep.inputs
          ((hierStep.children .secondDelay).outputs .output) := by
  have delayInput := ModuleStructure.child_input satisfies .secondDelay .input
  have muxRealizes := ModuleStructure.child_realizes satisfies .secondInputMux
  simp only [structuralChildren] at muxRealizes
  have muxResult := Mux.result_of_realization
    (FFTStageLane.dataSignalType dataFormat) muxRealizes
  change (hierStep.children .secondInputMux).outputs .result =
    bif (hierStep.children .secondInputMux).inputs .select then
      (hierStep.children .secondInputMux).inputs .whenTrue
    else (hierStep.children .secondInputMux).inputs .whenFalse at muxResult
  have select := ModuleStructure.child_input satisfies .secondInputMux .select
  have whenFalse := ModuleStructure.child_input satisfies
    .secondInputMux .whenFalse
  have whenTrue := ModuleStructure.child_input satisfies
    .secondInputMux .whenTrue
  change (hierStep.children .secondDelay).inputs .input =
    (hierStep.children .secondInputMux).outputs .result at delayInput
  change (hierStep.children .secondInputMux).inputs .select =
    hierStep.inputs .i_firstHalf at select
  change (hierStep.children .secondInputMux).inputs .whenFalse =
    (hierStep.children .secondDelay).outputs .output at whenFalse
  change (hierStep.children .secondInputMux).inputs .whenTrue =
    hierStep.inputs .i_branchB at whenTrue
  rw [delayInput, muxResult, select, whenFalse, whenTrue]
  rfl

theorem butterflyOperands_of_solution
    {hierStep : HierStep (laneStructure dataFormat twiddleFormat pairExponent
      phaseWidth laneAddressWidth lane twiddleDefinitionName twiddleValues
      pipeline)}
    (satisfies : (laneStructure dataFormat twiddleFormat pairExponent
      phaseWidth laneAddressWidth lane twiddleDefinitionName twiddleValues
      pipeline).IsSolution hierStep) :
    (hierStep.children .butterfly).inputs .a =
        (FFTStageLane.invocationValue dataFormat twiddleFormat phaseWidth
          hierStep.inputs ((hierStep.children .firstDelay).outputs .output)
          ((hierStep.children .secondDelay).outputs .output)).operands.a ∧
      (hierStep.children .butterfly).inputs .b =
        (FFTStageLane.invocationValue dataFormat twiddleFormat phaseWidth
          hierStep.inputs ((hierStep.children .firstDelay).outputs .output)
          ((hierStep.children .secondDelay).outputs .output)).operands.b := by
  have aInput := ModuleStructure.child_input satisfies .butterfly .a
  have bInput := ModuleStructure.child_input satisfies .butterfly .b
  have aRealizes := ModuleStructure.child_realizes satisfies .operandAMux
  have bRealizes := ModuleStructure.child_realizes satisfies .operandBMux
  simp only [structuralChildren] at aRealizes bRealizes
  have aResult := Mux.result_of_realization
    (FFTStageLane.dataSignalType dataFormat) aRealizes
  have bResult := Mux.result_of_realization
    (FFTStageLane.dataSignalType dataFormat) bRealizes
  change (hierStep.children .operandAMux).outputs .result =
    bif (hierStep.children .operandAMux).inputs .select then
      (hierStep.children .operandAMux).inputs .whenTrue
    else (hierStep.children .operandAMux).inputs .whenFalse at aResult
  change (hierStep.children .operandBMux).outputs .result =
    bif (hierStep.children .operandBMux).inputs .select then
      (hierStep.children .operandBMux).inputs .whenTrue
    else (hierStep.children .operandBMux).inputs .whenFalse at bResult
  have aSelect := ModuleStructure.child_input satisfies .operandAMux .select
  have aFalse := ModuleStructure.child_input satisfies .operandAMux .whenFalse
  have aTrue := ModuleStructure.child_input satisfies .operandAMux .whenTrue
  have bSelect := ModuleStructure.child_input satisfies .operandBMux .select
  have bFalse := ModuleStructure.child_input satisfies .operandBMux .whenFalse
  have bTrue := ModuleStructure.child_input satisfies .operandBMux .whenTrue
  change (hierStep.children .butterfly).inputs .a =
    (hierStep.children .operandAMux).outputs .result at aInput
  change (hierStep.children .butterfly).inputs .b =
    (hierStep.children .operandBMux).outputs .result at bInput
  change (hierStep.children .operandAMux).inputs .select =
    hierStep.inputs .i_firstHalf at aSelect
  change (hierStep.children .operandAMux).inputs .whenFalse =
    (hierStep.children .firstDelay).outputs .output at aFalse
  change (hierStep.children .operandAMux).inputs .whenTrue =
    (hierStep.children .secondDelay).outputs .output at aTrue
  change (hierStep.children .operandBMux).inputs .select =
    hierStep.inputs .i_firstHalf at bSelect
  change (hierStep.children .operandBMux).inputs .whenFalse =
    hierStep.inputs .i_branchA at bFalse
  change (hierStep.children .operandBMux).inputs .whenTrue =
    (hierStep.children .firstDelay).outputs .output at bTrue
  constructor
  · rw [aInput, aResult, aSelect, aFalse, aTrue]
    cases half : hierStep.inputs .i_firstHalf <;>
      simp [FFTStageLane.invocationValue, half]
  · rw [bInput, bResult, bSelect, bFalse, bTrue]
    cases half : hierStep.inputs .i_firstHalf <;>
      simp [FFTStageLane.invocationValue, half]

theorem butterflyTwiddle_of_solution
    {hierStep : HierStep (laneStructure dataFormat twiddleFormat pairExponent
      phaseWidth laneAddressWidth lane twiddleDefinitionName twiddleValues
      pipeline)}
    (satisfies : (laneStructure dataFormat twiddleFormat pairExponent
      phaseWidth laneAddressWidth lane twiddleDefinitionName twiddleValues
      pipeline).IsSolution hierStep) :
    (hierStep.children .butterfly).inputs .twiddle =
      twiddleValues (FFTStageLane.twiddleAddress phaseWidth laneAddressWidth lane
        (FFTStageLane.inputPhase phaseWidth
          (hierStep.inputs .i_outputPhase))) := by
  have butterflyInput := ModuleStructure.child_input satisfies .butterfly .twiddle
  have romInput := ModuleStructure.child_input satisfies .twiddle .address
  have concatLeft := ModuleStructure.child_input satisfies .addressConcat .left
  have concatRight := ModuleStructure.child_input satisfies .addressConcat .right
  have constantRealizes := ModuleStructure.child_realizes satisfies .laneAddress
  have concatRealizes := ModuleStructure.child_realizes satisfies .addressConcat
  have romRealizes := ModuleStructure.child_realizes satisfies .twiddle
  simp only [structuralChildren] at constantRealizes concatRealizes romRealizes
  obtain ⟨_, _, constantAllowed⟩ := Constant.allowed_of_realization
    (.vector laneAddressWidth .bit)
    (FFTStageLane.Internal.laneAddress laneAddressWidth lane) constantRealizes
  have constantOutput := Constant.output_of_allowed
    (.vector laneAddressWidth .bit)
    (FFTStageLane.Internal.laneAddress laneAddressWidth lane) constantAllowed
  have concatResult := VectorConcat.result_of_realization .bit
    laneAddressWidth phaseWidth concatRealizes
  have romData := ROM.data_of_realization twiddleDefinitionName
    (FFTStageLane.twiddleSignalType twiddleFormat)
    (laneAddressWidth + phaseWidth) twiddleValues romRealizes
  change (hierStep.children .butterfly).inputs .twiddle =
    (hierStep.children .twiddle).outputs .data at butterflyInput
  change (hierStep.children .twiddle).inputs .address =
    (hierStep.children .addressConcat).outputs .result at romInput
  change (hierStep.children .addressConcat).inputs .left =
    (hierStep.children .laneAddress).outputs .output at concatLeft
  change (hierStep.children .addressConcat).inputs .right =
    hierStep.inputs .i_outputPhase at concatRight
  change (hierStep.children .laneAddress).outputs .output =
    FFTStageLane.Internal.laneAddress laneAddressWidth lane at constantOutput
  change (hierStep.children .addressConcat).outputs .result =
    VectorConcat.concat
      ((hierStep.children .addressConcat).inputs .left)
      ((hierStep.children .addressConcat).inputs .right) at concatResult
  change (hierStep.children .twiddle).outputs .data =
    ROM.lookup (laneAddressWidth + phaseWidth) twiddleValues
      ((hierStep.children .twiddle).inputs .address) at romData
  rw [butterflyInput, romData, romInput, concatResult, concatLeft,
    constantOutput, concatRight]
  simp [ROM.lookup, FFTStageLane.twiddleAddress,
    FFTStageLane.Internal.laneAddress]
  apply congrArg twiddleValues
  apply Fin.ext
  rfl

theorem parentOutputs_of_solution
    {hierStep : HierStep (laneStructure dataFormat twiddleFormat pairExponent
      phaseWidth laneAddressWidth lane twiddleDefinitionName twiddleValues
      pipeline)}
    (satisfies : (laneStructure dataFormat twiddleFormat pairExponent
      phaseWidth laneAddressWidth lane twiddleDefinitionName twiddleValues
      pipeline).IsSolution hierStep) :
    hierStep.outputs .o_upper =
        (hierStep.children .butterfly).outputs .upper ∧
      hierStep.outputs .o_lower =
        (hierStep.children .butterfly).outputs .lower := by
  exact ⟨ModuleStructure.parent_output satisfies .o_upper,
    ModuleStructure.parent_output satisfies .o_lower⟩

end HTFFT.Silean.FFTStageLane.Internal
