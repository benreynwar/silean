import HTFFT.Silean.FFTStageControl.Internal.FFTStageControlStep
import Silean.Contracts.Cycle.CycleTrace
import Silean.Semantics.StructuralObservation

/-! Trace correctness of shared rolled-stage control. -/

namespace HTFFT.Silean.FFTStageControl.Internal

open _root_.Silean
open _root_.Silean.Modules
open HTFFT.Silean.FFTStage.Internal

private abbrev CounterState (phaseExponent : Nat) :=
  (EnabledResetCounter.cycleContract (phaseWidth phaseExponent)
    (phaseOne phaseExponent)).state.Values

private def controlState (phaseExponent : Nat)
    (inputCounter outputCounter : CounterState phaseExponent)
    (marker : Fin (FFTStageControl.pairDelay phaseExponent) → Bool) :
    FFTStageControl.State phaseExponent :=
  { phase := FFTStageControl.phaseOfBits phaseExponent
      (inputCounter .stored)
    outputPhase := FFTStageControl.phaseOfBits phaseExponent
      (outputCounter .stored)
    markerDelay := marker
    firstDelay := fun _ => ()
    secondDelay := fun _ => () }

private theorem controlStep
    (phaseExponent : Nat)
    {step : HierStep (moduleStructure phaseExponent)}
    (satisfies : (moduleStructure phaseExponent).IsSolution step)
    {inputCurrent inputNext outputCurrent outputNext :
      CounterState phaseExponent}
    {markerCurrent markerNext :
      Fin (FFTStageControl.pairDelay phaseExponent) → Bool}
    (inputAllowed :
      (EnabledResetCounter.cycleContract (phaseWidth phaseExponent)
        (phaseOne phaseExponent)).Allows {
          inputs := (step.children .inputPhaseCounter).inputs
          currentState := inputCurrent
          outputs := (step.children .inputPhaseCounter).outputs
          nextState := inputNext })
    (outputAllowed :
      (EnabledResetCounter.cycleContract (phaseWidth phaseExponent)
        (phaseOne phaseExponent)).Allows {
          inputs := (step.children .outputPhaseCounter).inputs
          currentState := outputCurrent
          outputs := (step.children .outputPhaseCounter).outputs
          nextState := outputNext })
    (markerStep : _root_.Silean.DelayLine.Step
      (FFTStageControl.pairDelay phaseExponent)
      ((step.children .markerDelay).inputs .input) markerCurrent
      ((step.children .markerDelay).outputs .output) markerNext) :
    FFTStageControl.Transition phaseExponent step.inputs
      (controlState phaseExponent inputCurrent outputCurrent markerCurrent)
      step.outputs
      (controlState phaseExponent inputNext outputNext markerNext) := by
  let markerValue : Bool := (step.children .markerDelay).outputs .output
  have inputWiring := inputCounterInputs_of_solution satisfies
  have outputWiring := outputCounterInputs_of_solution satisfies
  have markerInput := markerInput_of_solution satisfies
  have boundary := outputs_of_solution satisfies
  have inputValue := EnabledResetCounter.value_of_allowed inputAllowed
  have outputValue := EnabledResetCounter.value_of_allowed outputAllowed
  have inputNextValue := EnabledResetCounter.next_stored_of_allowed inputAllowed
  have outputNextValue := EnabledResetCounter.next_stored_of_allowed outputAllowed
  have outputReset :
      (step.children .outputPhaseCounter).inputs .reset = markerValue := by
    exact outputWiring.2
  have delayedBoundary : step.outputs .o_delayedFirst = markerValue := by
    exact boundary.1
  have outputPhaseBoundary : step.outputs .o_outputPhase =
      bif markerValue then phaseZero phaseExponent
      else (step.children .outputPhaseCounter).outputs .value := by
    exact boundary.2.1
  change (step.children .inputPhaseCounter).outputs .value =
    inputCurrent .stored at inputValue
  change (step.children .outputPhaseCounter).outputs .value =
    outputCurrent .stored at outputValue
  change inputNext .stored = EnabledResetCounter.nextValue
    (phaseWidth phaseExponent) (phaseOne phaseExponent)
    ((step.children .inputPhaseCounter).inputs .enable)
    ((step.children .inputPhaseCounter).inputs .reset)
    (inputCurrent .stored) at inputNextValue
  change outputNext .stored = EnabledResetCounter.nextValue
    (phaseWidth phaseExponent) (phaseOne phaseExponent)
    ((step.children .outputPhaseCounter).inputs .enable)
    ((step.children .outputPhaseCounter).inputs .reset)
    (outputCurrent .stored) at outputNextValue
  change _root_.Silean.DelayLine.Step (α := Bool)
    (FFTStageControl.pairDelay phaseExponent)
    ((step.children .markerDelay).inputs .input) markerCurrent
    markerValue markerNext at markerStep

  have markerOutput :
      markerValue =
        DelayLine.output (FFTStageControl.pairDelay phaseExponent)
          (FFTStageControl.pairDelay_pos phaseExponent) markerCurrent := by
    simpa [_root_.Silean.DelayLine.Step, DelayLine.output,
      FFTStageControl.pairDelay_pos] using markerStep.1
  have markerNextValue : markerNext =
      DelayLine.next (FFTStageControl.pairDelay phaseExponent)
        (step.inputs .i_first) markerCurrent := by
    funext index
    have shifted := markerStep.2 index
    rw [markerInput] at shifted
    exact shifted

  have inputEffective :
      FFTStageControl.phaseOfBits phaseExponent
          (bif step.inputs .i_first then phaseZero phaseExponent
            else inputCurrent .stored) =
        Commutator.effectivePhase (FFTStageControl.pairDelay phaseExponent)
          (FFTStageControl.pairDelay_pos phaseExponent)
          (FFTStageControl.phaseOfBits phaseExponent
            (inputCurrent .stored))
          (step.inputs .i_first) := by
    cases first : step.inputs .i_first <;>
      simp [Commutator.effectivePhase]
  have outputEffective :
      FFTStageControl.phaseOfBits phaseExponent
          (bif (DelayLine.output (FFTStageControl.pairDelay phaseExponent)
              (FFTStageControl.pairDelay_pos phaseExponent) markerCurrent)
            then phaseZero phaseExponent else outputCurrent .stored) =
        Commutator.effectivePhase (FFTStageControl.pairDelay phaseExponent)
          (FFTStageControl.pairDelay_pos phaseExponent)
          (FFTStageControl.phaseOfBits phaseExponent
            (outputCurrent .stored))
          (DelayLine.output (FFTStageControl.pairDelay phaseExponent)
            (FFTStageControl.pairDelay_pos phaseExponent) markerCurrent) := by
    cases first : DelayLine.output
        (FFTStageControl.pairDelay phaseExponent)
        (FFTStageControl.pairDelay_pos phaseExponent) markerCurrent <;>
      simp [Commutator.effectivePhase]

  constructor
  · unfold FFTStageControl.outputMatches
    change step.outputs .o_delayedFirst =
          DelayLine.output (FFTStageControl.pairDelay phaseExponent)
            (FFTStageControl.pairDelay_pos phaseExponent) markerCurrent ∧
      step.outputs .o_firstHalf =
          Commutator.inFirstHalf (FFTStageControl.pairDelay phaseExponent)
            (Commutator.effectivePhase
              (FFTStageControl.pairDelay phaseExponent)
              (FFTStageControl.pairDelay_pos phaseExponent)
              (FFTStageControl.phaseOfBits phaseExponent
                (inputCurrent .stored)) (step.inputs .i_first)) ∧
      step.outputs .o_outputPhase =
          FFTStageControl.phaseBits phaseExponent
            (Commutator.effectivePhase
              (FFTStageControl.pairDelay phaseExponent)
              (FFTStageControl.pairDelay_pos phaseExponent)
              (FFTStageControl.phaseOfBits phaseExponent
                (outputCurrent .stored))
              (DelayLine.output (FFTStageControl.pairDelay phaseExponent)
                (FFTStageControl.pairDelay_pos phaseExponent) markerCurrent))
    refine ⟨delayedBoundary.trans markerOutput, ?_, ?_⟩
    · rw [boundary.2.2, inputValue]
      rw [← FFTStageControl.inFirstHalf_phaseOfBits phaseExponent,
        inputEffective]
    · rw [outputPhaseBoundary, outputValue, markerOutput]
      rw [← FFTStageControl.phaseBits_phaseOfBits phaseExponent
        (bif DelayLine.output (FFTStageControl.pairDelay phaseExponent)
          (FFTStageControl.pairDelay_pos phaseExponent) markerCurrent then
            phaseZero phaseExponent else outputCurrent .stored),
        outputEffective]
  · unfold controlState Commutator.nextState
    dsimp only [Commutator.signals]
    congr 1
    · rw [inputNextValue, inputWiring.1, inputWiring.2]
      exact FFTStageControl.phaseOfBits_nextValue phaseExponent
        (inputCurrent .stored) (step.inputs .i_first)
    · rw [outputNextValue, outputWiring.1, outputReset, markerOutput]
      exact FFTStageControl.phaseOfBits_nextValue phaseExponent
        (outputCurrent .stored)
        (DelayLine.output (FFTStageControl.pairDelay phaseExponent)
          (FFTStageControl.pairDelay_pos phaseExponent) markerCurrent)

private theorem controlTrace
    (phaseExponent : Nat)
    (hierarchy : List (HierStep (moduleStructure phaseExponent)))
    (solutions : ∀ step ∈ hierarchy,
      (moduleStructure phaseExponent).IsSolution step)
    {inputInitial inputFinal outputInitial outputFinal :
      CounterState phaseExponent}
    {markerInitial markerFinal :
      Fin (FFTStageControl.pairDelay phaseExponent) → Bool}
    (inputTrace : Trace
      (EnabledResetCounter.cycleContract (phaseWidth phaseExponent)
        (phaseOne phaseExponent)).Transition inputInitial
      (hierarchy.map fun step => (step.children .inputPhaseCounter).inputs)
      (hierarchy.map fun step => (step.children .inputPhaseCounter).outputs)
      inputFinal)
    (outputTrace : Trace
      (EnabledResetCounter.cycleContract (phaseWidth phaseExponent)
        (phaseOne phaseExponent)).Transition outputInitial
      (hierarchy.map fun step => (step.children .outputPhaseCounter).inputs)
      (hierarchy.map fun step => (step.children .outputPhaseCounter).outputs)
      outputFinal)
    (markerTrace : Trace
      (_root_.Silean.DelayLine.Step
        (FFTStageControl.pairDelay phaseExponent)) markerInitial
      ((hierarchy.map fun step => (step.children .markerDelay).inputs).map
        fun input => input .input)
      ((hierarchy.map fun step => (step.children .markerDelay).outputs).map
        fun output => output .output)
      markerFinal) :
    Trace (FFTStageControl.Transition phaseExponent)
      (controlState phaseExponent inputInitial outputInitial markerInitial)
      (hierarchy.map HierStep.inputs) (hierarchy.map HierStep.outputs)
      (controlState phaseExponent inputFinal outputFinal markerFinal) := by
  induction hierarchy generalizing inputInitial outputInitial markerInitial with
  | nil =>
      cases inputTrace
      cases outputTrace
      cases markerTrace
      exact .nil _
  | cons step hierarchy induction =>
      cases inputTrace with
      | cons _ _ inputAllowed inputRest =>
        cases outputTrace with
        | cons _ _ outputAllowed outputRest =>
          cases markerTrace with
          | cons _ _ markerStep markerRest =>
            refine .cons step.inputs step.outputs
              (controlStep phaseExponent (solutions step (by simp))
                inputAllowed outputAllowed markerStep) ?_
            apply induction
            · intro later member
              exact solutions later (by simp [member])
            · exact inputRest
            · exact outputRest
            · exact markerRest

/-- Every concrete shared-control execution follows the pure commutator's
control projection from some hidden initial state. -/
theorem contract_of_execution
    (phaseExponent : Nat)
    {initialState finalState : (moduleStructure phaseExponent).State}
    {inputs : List
      (FFTStageControl.ports (phaseWidth phaseExponent)).inputs.Values}
    {outputs : List
      (FFTStageControl.ports (phaseWidth phaseExponent)).outputs.Values}
    (execution : (moduleStructure phaseExponent).Executes
      initialState inputs outputs finalState) :
    FFTStageControl.contract phaseExponent execution.toBoundaryTrace := by
  obtain ⟨hierarchy, observed, rootOutputs⟩ := execution.observe
  let inputExecution := observed.child .inputPhaseCounter
  let outputExecution := observed.child .outputPhaseCounter
  let markerExecution := observed.child .markerDelay
  simp only [structuralChildren] at inputExecution outputExecution markerExecution

  have inputAccepted :=
    (EnabledResetCounter.certification (phaseWidth phaseExponent)
      (phaseOne phaseExponent)).accepts_of_executes inputExecution
  have outputAccepted :=
    (EnabledResetCounter.certification (phaseWidth phaseExponent)
      (phaseOne phaseExponent)).accepts_of_executes outputExecution
  obtain ⟨inputInitial, inputFinal, inputTrace⟩ := inputAccepted
  obtain ⟨outputInitial, outputFinal, outputTrace⟩ := outputAccepted
  obtain ⟨markerInitial, markerFinal, markerTrace⟩ :=
    ShiftRegister.delayTrace_of_execution .bit
      (FFTStageControl.pairDelay phaseExponent)
      (FFTStageControl.pairDelay_pos phaseExponent) markerExecution

  have parentTrace := controlTrace phaseExponent hierarchy
    (fun step member => observed.solution_of_mem step member)
    inputTrace outputTrace markerTrace
  unfold FFTStageControl.contract
  simp only [Trace.toBoundaryTrace_inputs, Trace.toBoundaryTrace_outputs]
  refine ⟨controlState phaseExponent inputInitial outputInitial markerInitial,
    controlState phaseExponent inputFinal outputFinal markerFinal, ?_⟩
  rw [← observed.hierarchy_inputs, ← rootOutputs]
  exact parentTrace

end HTFFT.Silean.FFTStageControl.Internal
