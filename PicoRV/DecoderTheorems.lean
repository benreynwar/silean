import PicoRV.Internal.DecoderVerification

/-! # PicoRV decoder theorems

This is the supported proof interface for the complete two-stage decoder.
Its schedules, child hierarchy, and state correspondence proof remain under
`Internal/`.
-/

namespace PicoRV.Decoder

open Silean

section AllowedStep

variable {step : cycleContract.Step} (allowed : cycleContract.Allows step)

include allowed

/-- Decoder outputs expose the values held before the current clock edge. -/
theorem outputs_of_allowed : step.outputs = outputValues step.currentState :=
  (outputRule_holds_iff step.inputs step.currentState step.outputs).mp
    (allowed.1 .outputs)

/-- The two decoder stages advance together according to the source-level
transition function in `Decoder.lean`. -/
theorem nextState_of_allowed :
    step.nextState = nextState (valuesOf step.inputs) step.currentState := by
  rw [allowed.2]
  rfl

end AllowedStep

/-- The authored two-stage hierarchy implements the decoder cycle contract. -/
theorem implements_contract :
    Silean.Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

/-- Structural equations for the complete decoder hierarchy have one solution
for each boundary input and physical state. -/
theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨certified.hasStructuralResult, certified.structuralResultUnique⟩

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end PicoRV.Decoder
