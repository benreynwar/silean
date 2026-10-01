import HTFFT.Silean.FFTStageControl.FFTStageControlContract
import HTFFT.Silean.FFTStageControl.Internal.FFTStageControlStructural

/-! One-cycle structural equations for shared rolled-stage control. -/

namespace HTFFT.Silean.FFTStageControl.Internal

open _root_.Silean
open _root_.Silean.Modules

variable {phaseExponent : Nat}

/-- The input phase counter is permanently enabled and reset by `i_first`. -/
theorem inputCounterInputs_of_solution
    {step : HierStep (moduleStructure phaseExponent)}
    (satisfies : (moduleStructure phaseExponent).IsSolution step) :
    (step.children .inputPhaseCounter).inputs .enable = true ∧
      (step.children .inputPhaseCounter).inputs .reset = step.inputs .i_first := by
  have enable := ModuleStructure.child_input satisfies .inputPhaseCounter .enable
  have reset := ModuleStructure.child_input satisfies .inputPhaseCounter .reset
  have trueRealizes := ModuleStructure.child_realizes satisfies .trueSource
  simp only [structuralChildren] at trueRealizes
  have trueOutput : (step.children .trueSource).outputs .output = true := by
    let certification := (Primitives.constantCertified true).certification
    obtain ⟨current, corresponds⟩ := certification.hasCorrespondingState
      (step.children .trueSource).currentState
    obtain ⟨_, allowed, _⟩ := certification.allows_of_realizes current
      (step.children .trueSource).step corresponds trueRealizes
    exact (Primitives.constantOutputRule_holds_iff true _ _ _).mp
      (allowed.1 .apply)
  change (step.children .inputPhaseCounter).inputs .enable =
    (step.children .trueSource).outputs .output at enable
  change (step.children .inputPhaseCounter).inputs .reset =
    step.inputs .i_first at reset
  exact ⟨enable.trans trueOutput, reset⟩

/-- The marker delay receives the boundary marker directly. -/
theorem markerInput_of_solution
    {step : HierStep (moduleStructure phaseExponent)}
    (satisfies : (moduleStructure phaseExponent).IsSolution step) :
    (step.children .markerDelay).inputs .input = step.inputs .i_first := by
  exact ModuleStructure.child_input satisfies .markerDelay .input

/-- The output phase counter is permanently enabled and resets when the
delayed marker reaches the commutator output boundary. -/
theorem outputCounterInputs_of_solution
    {step : HierStep (moduleStructure phaseExponent)}
    (satisfies : (moduleStructure phaseExponent).IsSolution step) :
    (step.children .outputPhaseCounter).inputs .enable = true ∧
      (step.children .outputPhaseCounter).inputs .reset =
        (step.children .markerDelay).outputs .output := by
  have enable := ModuleStructure.child_input satisfies .outputPhaseCounter .enable
  have reset := ModuleStructure.child_input satisfies .outputPhaseCounter .reset
  have trueRealizes := ModuleStructure.child_realizes satisfies .trueSource
  simp only [structuralChildren] at trueRealizes
  have trueOutput : (step.children .trueSource).outputs .output = true := by
    let certification := (Primitives.constantCertified true).certification
    obtain ⟨current, corresponds⟩ := certification.hasCorrespondingState
      (step.children .trueSource).currentState
    obtain ⟨_, allowed, _⟩ := certification.allows_of_realizes current
      (step.children .trueSource).step corresponds trueRealizes
    exact (Primitives.constantOutputRule_holds_iff true _ _ _).mp
      (allowed.1 .apply)
  change (step.children .outputPhaseCounter).inputs .enable =
    (step.children .trueSource).outputs .output at enable
  change (step.children .outputPhaseCounter).inputs .reset =
    (step.children .markerDelay).outputs .output at reset
  exact ⟨enable.trans trueOutput, reset⟩

/-- Boundary outputs and the two selected phase words are the advertised
combinational functions of the counters and delayed marker. -/
theorem outputs_of_solution
    {step : HierStep (moduleStructure phaseExponent)}
    (satisfies : (moduleStructure phaseExponent).IsSolution step) :
    step.outputs .o_delayedFirst =
        (step.children .markerDelay).outputs .output ∧
      step.outputs .o_outputPhase =
        (bif (step.children .markerDelay).outputs .output then
          phaseZero phaseExponent
        else (step.children .outputPhaseCounter).outputs .value) ∧
      step.outputs .o_firstHalf =
        !((bif step.inputs .i_first then phaseZero phaseExponent
          else (step.children .inputPhaseCounter).outputs .value)
            (Fin.last phaseExponent)) := by
  have delayed := ModuleStructure.parent_output satisfies .o_delayedFirst
  have outputPhase := ModuleStructure.parent_output satisfies .o_outputPhase
  have firstHalf := ModuleStructure.parent_output satisfies .o_firstHalf

  have zeroRealizes := ModuleStructure.child_realizes satisfies .phaseZero
  have inputMuxRealizes := ModuleStructure.child_realizes satisfies .inputPhaseSelect
  have outputMuxRealizes := ModuleStructure.child_realizes satisfies .outputPhaseSelect
  have splitterRealizes := ModuleStructure.child_realizes satisfies .inputPhaseSplit
  have notRealizes := ModuleStructure.child_realizes satisfies .firstHalf
  simp only [structuralChildren] at zeroRealizes inputMuxRealizes outputMuxRealizes splitterRealizes notRealizes

  obtain ⟨_, _, zeroAllowed⟩ := Constant.allowed_of_realization
    (.vector (phaseWidth phaseExponent) .bit) (phaseZero phaseExponent)
      zeroRealizes
  have zeroOutput := Constant.output_of_allowed
    (.vector (phaseWidth phaseExponent) .bit) (phaseZero phaseExponent)
      zeroAllowed
  have inputMux := Mux.result_of_realization
    (.vector (phaseWidth phaseExponent) .bit) inputMuxRealizes
  have outputMux := Mux.result_of_realization
    (.vector (phaseWidth phaseExponent) .bit) outputMuxRealizes

  have inputSelect := ModuleStructure.child_input satisfies .inputPhaseSelect .select
  have inputFalse := ModuleStructure.child_input satisfies .inputPhaseSelect .whenFalse
  have inputTrue := ModuleStructure.child_input satisfies .inputPhaseSelect .whenTrue
  have outputSelect := ModuleStructure.child_input satisfies .outputPhaseSelect .select
  have outputFalse := ModuleStructure.child_input satisfies .outputPhaseSelect .whenFalse
  have outputTrue := ModuleStructure.child_input satisfies .outputPhaseSelect .whenTrue
  have splitInput := ModuleStructure.child_input satisfies .inputPhaseSplit .value
  have notInput := ModuleStructure.child_input satisfies .firstHalf .input

  change (step.children .inputPhaseSelect).outputs .result =
    bif (step.children .inputPhaseSelect).inputs .select then
      (step.children .inputPhaseSelect).inputs .whenTrue
    else (step.children .inputPhaseSelect).inputs .whenFalse at inputMux
  change (step.children .outputPhaseSelect).outputs .result =
    bif (step.children .outputPhaseSelect).inputs .select then
      (step.children .outputPhaseSelect).inputs .whenTrue
    else (step.children .outputPhaseSelect).inputs .whenFalse at outputMux
  change (step.children .phaseZero).outputs .output =
    phaseZero phaseExponent at zeroOutput
  change (step.children .inputPhaseSplit).inputs .value =
    (step.children .inputPhaseSelect).outputs .result at splitInput
  change (step.children .firstHalf).inputs .input =
    (step.children .inputPhaseSplit).outputs (Fin.last phaseExponent) at notInput

  have splitOutput :
      (step.children .inputPhaseSplit).outputs (Fin.last phaseExponent) =
        (step.children .inputPhaseSplit).inputs .value
          (Fin.last phaseExponent) := by
    let certification := (phaseSplitter phaseExponent).certified.certification
    obtain ⟨current, corresponds⟩ := certification.hasCorrespondingState
      (step.children .inputPhaseSplit).currentState
    obtain ⟨_, allowed, _⟩ := certification.allows_of_realizes current
      (step.children .inputPhaseSplit).step corresponds splitterRealizes
    have outputsEqual := (Composition.SignalSplitter.outputRule_holds_iff
      (phaseSplitter phaseExponent) _ _ _).mp (allowed.1 .apply)
    exact congrFun outputsEqual (Fin.last phaseExponent)
  have notOutput : (step.children .firstHalf).outputs .output =
      !(step.children .firstHalf).inputs .input := by
    let certification := Primitives.notCertified.certification
    obtain ⟨current, corresponds⟩ := certification.hasCorrespondingState
      (step.children .firstHalf).currentState
    obtain ⟨_, allowed, _⟩ := certification.allows_of_realizes current
      (step.children .firstHalf).step corresponds notRealizes
    exact (Primitives.notOutputRule_holds_iff _ _ _).mp
      (allowed.1 .apply)

  change step.outputs .o_delayedFirst =
    (step.children .markerDelay).outputs .output at delayed
  change step.outputs .o_outputPhase =
    (step.children .outputPhaseSelect).outputs .result at outputPhase
  change step.outputs .o_firstHalf =
    (step.children .firstHalf).outputs .output at firstHalf
  change (step.children .inputPhaseSelect).inputs .select =
    step.inputs .i_first at inputSelect
  change (step.children .inputPhaseSelect).inputs .whenFalse =
    (step.children .inputPhaseCounter).outputs .value at inputFalse
  change (step.children .inputPhaseSelect).inputs .whenTrue =
    (step.children .phaseZero).outputs .output at inputTrue
  change (step.children .outputPhaseSelect).inputs .select =
    (step.children .markerDelay).outputs .output at outputSelect
  change (step.children .outputPhaseSelect).inputs .whenFalse =
    (step.children .outputPhaseCounter).outputs .value at outputFalse
  change (step.children .outputPhaseSelect).inputs .whenTrue =
    (step.children .phaseZero).outputs .output at outputTrue

  refine ⟨delayed, ?_, ?_⟩
  · rw [outputPhase, outputMux, outputSelect, outputFalse, outputTrue,
      zeroOutput]
    rfl
  · rw [firstHalf, notOutput, notInput, splitOutput, splitInput, inputMux,
      inputSelect, inputFalse, inputTrue, zeroOutput]
    rfl

end HTFFT.Silean.FFTStageControl.Internal
