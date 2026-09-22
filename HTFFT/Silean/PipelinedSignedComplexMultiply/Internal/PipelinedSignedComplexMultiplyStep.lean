import HTFFT.Silean.PipelinedSignedComplexMultiply.Internal.PipelinedSignedComplexMultiplyArithmetic
import HTFFT.Silean.PipelinedSignedComplexMultiply.Internal.PipelinedSignedComplexMultiplyStructural

/-! One-cycle structural consequences used by the multiplier trace proof. -/

namespace HTFFT.Silean.PipelinedSignedComplexMultiply.Internal

open _root_.Silean
open _root_.Silean.Modules

def numeratorPairCircuitValue
    (leftWidth rightWidth : Nat)
    (realReal imagImag realImag imagReal :
      Fin (productWidth leftWidth rightWidth) → Bool) :
    Fin 2 → Fin (numeratorWidth leftWidth rightWidth) → Bool :=
  fun index =>
    if index.val = 0 then
      Sub.resultValue
        (productWidth leftWidth rightWidth)
        (productWidth leftWidth rightWidth) true true true
        realReal imagImag
    else
      Add.resultValue
        (productWidth leftWidth rightWidth)
        (productWidth leftWidth rightWidth) true true true
        realImag imagReal

private theorem combinerOutput_of_solution
    (leftWidth rightWidth discardedWidth multiplierLatency : Nat)
    (registerBeforeRounding : Bool)
    {hierStep : HierStep
      (moduleStructure leftWidth rightWidth discardedWidth multiplierLatency
        registerBeforeRounding)}
    (satisfies :
      (moduleStructure leftWidth rightWidth discardedWidth multiplierLatency
        registerBeforeRounding).IsSolution hierStep) :
    (hierStep.children .numeratorCombine).outputs .value =
      fun index => (hierStep.children .numeratorCombine).inputs index := by
  let splitter := numeratorSplitter leftWidth rightWidth
  have realizes := ModuleStructure.child_realizes satisfies (.numeratorCombine)
  simp only [structuralChildren] at realizes
  obtain ⟨_, allowed, _⟩ :=
    splitter.combiner.certified.certification.allows_of_realizes
      SignalMap.emptyValues (hierStep.children .numeratorCombine).step
      trivial realizes
  have equation := (splitter.combiner.outputRule_holds_iff _ _ _).mp
    (allowed.1 Composition.SignalComponentRule.apply)
  change (hierStep.children .numeratorCombine).outputs =
    splitter.combiner.outputValues
      (hierStep.children .numeratorCombine).inputs at equation
  exact congrFun equation .value

private theorem splitterOutput_of_solution
    (leftWidth rightWidth discardedWidth multiplierLatency : Nat)
    (registerBeforeRounding : Bool)
    {hierStep : HierStep
      (moduleStructure leftWidth rightWidth discardedWidth multiplierLatency
        registerBeforeRounding)}
    (satisfies :
      (moduleStructure leftWidth rightWidth discardedWidth multiplierLatency
        registerBeforeRounding).IsSolution hierStep) :
    ∀ index,
      (hierStep.children .numeratorSplit).outputs index =
        (hierStep.children .numeratorSplit).inputs .value index := by
  let splitter := numeratorSplitter leftWidth rightWidth
  have realizes := ModuleStructure.child_realizes satisfies (.numeratorSplit)
  simp only [structuralChildren] at realizes
  obtain ⟨_, allowed, _⟩ :=
    splitter.certified.certification.allows_of_realizes
      SignalMap.emptyValues (hierStep.children .numeratorSplit).step
      trivial realizes
  have equation := (splitter.outputRule_holds_iff _ _ _).mp
    (allowed.1 Composition.SignalComponentRule.apply)
  change (hierStep.children .numeratorSplit).outputs =
    splitter.outputValues (hierStep.children .numeratorSplit).inputs at equation
  intro index
  exact congrFun equation index

theorem numeratorDelayInput_of_solution
    (leftWidth rightWidth discardedWidth multiplierLatency : Nat)
    (registerBeforeRounding : Bool)
    {hierStep : HierStep
      (moduleStructure leftWidth rightWidth discardedWidth multiplierLatency
        registerBeforeRounding)}
    (satisfies :
      (moduleStructure leftWidth rightWidth discardedWidth multiplierLatency
        registerBeforeRounding).IsSolution hierStep) :
    (hierStep.children .numeratorDelay).inputs .input =
      numeratorPairCircuitValue leftWidth rightWidth
        ((hierStep.children .realReal).outputs .result)
        ((hierStep.children .imagImag).outputs .result)
        ((hierStep.children .realImag).outputs .result)
        ((hierStep.children .imagReal).outputs .result) := by
  have realNumeratorRealizes :=
    ModuleStructure.child_realizes satisfies (.realNumerator)
  simp only [structuralChildren] at realNumeratorRealizes
  have realNumeratorEquation := Sub.result_of_realization
    (productWidth leftWidth rightWidth)
    (productWidth leftWidth rightWidth) true true true
    realNumeratorRealizes
  have realLeft := ModuleStructure.child_input satisfies (.realNumerator) (.left)
  have realRight := ModuleStructure.child_input satisfies (.realNumerator) (.right)
  change (hierStep.children .realNumerator).inputs .left =
    (hierStep.children .realReal).outputs .result at realLeft
  change (hierStep.children .realNumerator).inputs .right =
    (hierStep.children .imagImag).outputs .result at realRight
  change (hierStep.children .realNumerator).outputs .result =
    Sub.resultValue
      (productWidth leftWidth rightWidth)
      (productWidth leftWidth rightWidth) true true true
      ((hierStep.children .realNumerator).inputs .left)
      ((hierStep.children .realNumerator).inputs .right) at realNumeratorEquation
  rw [realLeft, realRight] at realNumeratorEquation

  have imagNumeratorRealizes :=
    ModuleStructure.child_realizes satisfies (.imagNumerator)
  simp only [structuralChildren] at imagNumeratorRealizes
  have imagNumeratorEquation := Add.result_of_realization
    (productWidth leftWidth rightWidth)
    (productWidth leftWidth rightWidth) true true true
    imagNumeratorRealizes
  have imagLeft := ModuleStructure.child_input satisfies (.imagNumerator) (.left)
  have imagRight := ModuleStructure.child_input satisfies (.imagNumerator) (.right)
  change (hierStep.children .imagNumerator).inputs .left =
    (hierStep.children .realImag).outputs .result at imagLeft
  change (hierStep.children .imagNumerator).inputs .right =
    (hierStep.children .imagReal).outputs .result at imagRight
  change (hierStep.children .imagNumerator).outputs .result =
    Add.resultValue
      (productWidth leftWidth rightWidth)
      (productWidth leftWidth rightWidth) true true true
      ((hierStep.children .imagNumerator).inputs .left)
      ((hierStep.children .imagNumerator).inputs .right) at imagNumeratorEquation
  rw [imagLeft, imagRight] at imagNumeratorEquation

  have combined := combinerOutput_of_solution leftWidth rightWidth
    discardedWidth multiplierLatency registerBeforeRounding satisfies
  have delayInput := ModuleStructure.child_input satisfies
    (.numeratorDelay) (.input)
  change (hierStep.children .numeratorDelay).inputs .input =
    (hierStep.children .numeratorCombine).outputs .value at delayInput
  rw [delayInput, combined]
  funext index
  change Fin 2 at index
  fin_cases index
  ·
    have combineInput := ModuleStructure.child_input satisfies
      (.numeratorCombine) (⟨0, by omega⟩)
    change (hierStep.children .numeratorCombine).inputs ⟨0, by omega⟩ =
      (hierStep.children .realNumerator).outputs .result at combineInput
    simpa [numeratorPairCircuitValue] using
      combineInput.trans realNumeratorEquation
  ·
    have combineInput := ModuleStructure.child_input satisfies
      (.numeratorCombine) (⟨1, by omega⟩)
    change (hierStep.children .numeratorCombine).inputs ⟨1, by omega⟩ =
      (hierStep.children .imagNumerator).outputs .result at combineInput
    simpa [numeratorPairCircuitValue] using
      combineInput.trans imagNumeratorEquation

theorem circuitOutputs_of_solution
    (leftWidth rightWidth discardedWidth multiplierLatency : Nat)
    (registerBeforeRounding : Bool)
    {hierStep : HierStep
      (moduleStructure leftWidth rightWidth discardedWidth multiplierLatency
        registerBeforeRounding)}
    (satisfies :
      (moduleStructure leftWidth rightWidth discardedWidth multiplierLatency
        registerBeforeRounding).IsSolution hierStep) :
    hierStep.outputs .resultReal =
        roundedNumeratorCircuitValue leftWidth rightWidth discardedWidth
          ((hierStep.children .numeratorDelay).outputs .output ⟨0, by omega⟩) ∧
      hierStep.outputs .resultImag =
        roundedNumeratorCircuitValue leftWidth rightWidth discardedWidth
          ((hierStep.children .numeratorDelay).outputs .output ⟨1, by omega⟩) := by
  have splitInput := ModuleStructure.child_input satisfies
    (.numeratorSplit) (.value)
  change (hierStep.children .numeratorSplit).inputs .value =
    (hierStep.children .numeratorDelay).outputs .output at splitInput
  have splitOutput := splitterOutput_of_solution leftWidth rightWidth
    discardedWidth multiplierLatency registerBeforeRounding satisfies

  have realLayoutRealizes := ModuleStructure.child_realizes satisfies
    (.realRoundInput)
  simp only [structuralChildren] at realLayoutRealizes
  have realLayoutEquation := VectorLayout.output_of_realization
    (numeratorWidth leftWidth rightWidth)
    (roundInputWidth leftWidth rightWidth discardedWidth)
    (roundInputLayout leftWidth rightWidth discardedWidth)
    realLayoutRealizes
  have imagLayoutRealizes := ModuleStructure.child_realizes satisfies
    (.imagRoundInput)
  simp only [structuralChildren] at imagLayoutRealizes
  have imagLayoutEquation := VectorLayout.output_of_realization
    (numeratorWidth leftWidth rightWidth)
    (roundInputWidth leftWidth rightWidth discardedWidth)
    (roundInputLayout leftWidth rightWidth discardedWidth)
    imagLayoutRealizes
  have realLayoutInput := ModuleStructure.child_input satisfies
    (.realRoundInput) (.input)
  change (hierStep.children .realRoundInput).inputs .input =
    (hierStep.children .numeratorSplit).outputs ⟨0, by omega⟩ at realLayoutInput
  have imagLayoutInput := ModuleStructure.child_input satisfies
    (.imagRoundInput) (.input)
  change (hierStep.children .imagRoundInput).inputs .input =
    (hierStep.children .numeratorSplit).outputs ⟨1, by omega⟩ at imagLayoutInput
  change (hierStep.children .realRoundInput).outputs .output =
    VectorLayout.apply (roundInputLayout leftWidth rightWidth discardedWidth)
      ((hierStep.children .realRoundInput).inputs .input) at realLayoutEquation
  change (hierStep.children .imagRoundInput).outputs .output =
    VectorLayout.apply (roundInputLayout leftWidth rightWidth discardedWidth)
      ((hierStep.children .imagRoundInput).inputs .input) at imagLayoutEquation

  have realRoundRealizes := ModuleStructure.child_realizes satisfies (.realRound)
  simp only [structuralChildren] at realRoundRealizes
  have realRoundEquation := SignedRoundShift.result_of_realization
    (resultWidth leftWidth rightWidth discardedWidth)
    (effectiveDiscard leftWidth rightWidth discardedWidth) realRoundRealizes
  have realRoundInput := ModuleStructure.child_input satisfies (.realRound) (.value)
  change (hierStep.children .realRound).inputs .value =
    (hierStep.children .realRoundInput).outputs .output at realRoundInput
  change (hierStep.children .realRound).outputs .result =
    SignedRoundShift.resultValue
      (resultWidth leftWidth rightWidth discardedWidth)
      (effectiveDiscard leftWidth rightWidth discardedWidth)
      ((hierStep.children .realRound).inputs .value) at realRoundEquation

  have imagRoundRealizes := ModuleStructure.child_realizes satisfies (.imagRound)
  simp only [structuralChildren] at imagRoundRealizes
  have imagRoundEquation := SignedRoundShift.result_of_realization
    (resultWidth leftWidth rightWidth discardedWidth)
    (effectiveDiscard leftWidth rightWidth discardedWidth) imagRoundRealizes
  have imagRoundInput := ModuleStructure.child_input satisfies (.imagRound) (.value)
  change (hierStep.children .imagRound).inputs .value =
    (hierStep.children .imagRoundInput).outputs .output at imagRoundInput
  change (hierStep.children .imagRound).outputs .result =
    SignedRoundShift.resultValue
      (resultWidth leftWidth rightWidth discardedWidth)
      (effectiveDiscard leftWidth rightWidth discardedWidth)
      ((hierStep.children .imagRound).inputs .value) at imagRoundEquation

  have parentReal := ModuleStructure.parent_output satisfies (.resultReal)
  have parentImag := ModuleStructure.parent_output satisfies (.resultImag)
  change hierStep.outputs .resultReal =
    (hierStep.children .realRound).outputs .result at parentReal
  change hierStep.outputs .resultImag =
    (hierStep.children .imagRound).outputs .result at parentImag

  constructor
  · rw [parentReal, realRoundEquation, realRoundInput, realLayoutEquation,
      realLayoutInput, splitOutput ⟨0, by omega⟩, splitInput]
    rfl
  · rw [parentImag, imagRoundEquation, imagRoundInput, imagLayoutEquation,
      imagLayoutInput, splitOutput ⟨1, by omega⟩, splitInput]
    rfl

end HTFFT.Silean.PipelinedSignedComplexMultiply.Internal
