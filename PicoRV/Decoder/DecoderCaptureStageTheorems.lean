import PicoRV.Decoder.Internal.DecoderCaptureStageVerification

/-! # Decoder capture-stage theorems

This is the supported proof interface for the registered capture stage. Its
child schedules and the relation between contract state and child-register
state remain under `Internal/`.
-/

namespace PicoRV.Decoder.CaptureStage

open Silean

section AllowedStep

variable {step : cycleContract.Step}
  (allowed : cycleContract.Allows step)

include allowed

/-- The stage exposes the values held before the current clock edge. -/
theorem outputs_of_allowed : step.outputs = step.currentState :=
  (outputRule_holds_iff step.inputs step.currentState step.outputs).mp
    (allowed.1 .outputs)

/-- The next state captures a completed instruction read, with reset affecting
the branch-class flag exactly as specified by `nextState`. -/
theorem nextState_of_allowed :
    step.nextState = nextState (valuesOf step.inputs) step.currentState := by
  rw [allowed.2]
  rfl

end AllowedStep

theorem implements_contract :
    Silean.Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨certified.hasStructuralResult, certified.structuralResultUnique⟩

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end PicoRV.Decoder.CaptureStage
