import HTFFT.Silean.UnrolledFFTNetwork.Internal.UnrolledFFTNetworkStructural

/-! One-cycle wiring equations for the generic unrolled network. -/

namespace HTFFT.Silean.UnrolledFFTNetwork.Internal

open _root_.Silean

variable {depth : Nat}
  {configuration : UnrolledFFT.Configuration depth}
  {table : HTFFT.Fixed.TwiddleTable depth}

@[simp] private theorem castDenote_self {signalType : SignalType}
    (equal : signalType = signalType) (value : signalType.Denote) :
    equal ▸ value = value := by
  have proofEqual : equal = rfl := Subsingleton.elim _ _
  rw [proofEqual]

private def castSignalValue {sourceType targetType : SignalType}
    (equal : sourceType = targetType) (value : sourceType.Denote) :
    targetType.Denote :=
  equal ▸ value

/-- Boundary zero receives the parent input directly. -/
theorem initialBoundaryInput_of_solution
    {hierStep : HierStep (moduleStructure depth configuration table)}
    (satisfies :
      (moduleStructure depth configuration table).IsSolution hierStep) :
    (hierStep.children (.boundaryDelay 0)).inputs .input =
      hierStep.inputs .input := by
  have input := ModuleStructure.child_input satisfies
    (.boundaryDelay 0) (.input)
  have zero : (0 : Fin (depth + 1)).val = 0 := rfl
  simp only [wiring, dif_pos zero, SignalSource.value_castType] at input
  simpa [EndpointContext.instanceOutput, SignalSource.value,
    castDenote_self] using input

/-- Every layer receives the output of the delay at its input boundary. -/
theorem layerInput_of_solution
    {hierStep : HierStep (moduleStructure depth configuration table)}
    (satisfies :
      (moduleStructure depth configuration table).IsSolution hierStep)
    (stage : Fin depth) :
    (hierStep.children (.layer stage)).inputs .input =
      (hierStep.children (.boundaryDelay stage.castSucc)).outputs .output := by
  have input := ModuleStructure.child_input satisfies
    (.layer stage) (.input)
  simpa [wiring, EndpointContext.instanceOutput, SignalSource.value] using input

/-- The successor boundary delay receives the preceding layer output. -/
theorem successorBoundaryInput_of_solution
    {hierStep : HierStep (moduleStructure depth configuration table)}
    (satisfies :
      (moduleStructure depth configuration table).IsSolution hierStep)
    (stage : Fin depth) :
    (hierStep.children (.boundaryDelay stage.succ)).inputs .input =
      (hierStep.children (.layer stage)).outputs .output := by
  have nonzero : (stage.succ : Fin (depth + 1)).val ≠ 0 := by simp
  have input := ModuleStructure.child_input satisfies
    (.boundaryDelay stage.succ) (.input)
  simp only [wiring, dif_neg nonzero, SignalSource.value_castType] at input
  change (hierStep.children (.boundaryDelay stage.succ)).inputs .input =
    castSignalValue (samplesType_eq configuration
      (previousStage_succ stage.succ nonzero))
      ((hierStep.children
        (.layer (previousStage stage.succ nonzero))).outputs .output) at input
  have previousEqual := previousStage_of_succ stage nonzero
  have castEqual :
      castSignalValue (samplesType_eq configuration
        (previousStage_succ stage.succ nonzero))
        ((hierStep.children
          (.layer (previousStage stage.succ nonzero))).outputs .output) =
      (hierStep.children (.layer stage)).outputs .output := by
    have outputHEq :
        ((hierStep.children
          (.layer (previousStage stage.succ nonzero))).outputs .output) ≍
        (hierStep.children (.layer stage)).outputs .output := by
      cases previousEqual
      rfl
    have transportedHEq :
        castSignalValue (samplesType_eq configuration
          (previousStage_succ stage.succ nonzero))
          ((hierStep.children
            (.layer (previousStage stage.succ nonzero))).outputs .output) ≍
        ((hierStep.children
          (.layer (previousStage stage.succ nonzero))).outputs .output) := by
      unfold castSignalValue
      change cast (congrArg SignalType.Denote
        (samplesType_eq configuration
          (previousStage_succ stage.succ nonzero)))
          ((hierStep.children
            (.layer (previousStage stage.succ nonzero))).outputs .output) ≍
        ((hierStep.children
          (.layer (previousStage stage.succ nonzero))).outputs .output)
      exact cast_heq _ _
    exact eq_of_heq (transportedHEq.trans outputHEq)
  exact input.trans castEqual

/-- The parent output is the final boundary-delay output. -/
theorem output_of_solution
    {hierStep : HierStep (moduleStructure depth configuration table)}
    (satisfies :
      (moduleStructure depth configuration table).IsSolution hierStep) :
    hierStep.outputs .output =
      (hierStep.children (.boundaryDelay (Fin.last depth))).outputs .output := by
  have output := ModuleStructure.parent_output satisfies (.output)
  simpa [wiring, EndpointContext.instanceOutput, SignalSource.value] using output

end HTFFT.Silean.UnrolledFFTNetwork.Internal
