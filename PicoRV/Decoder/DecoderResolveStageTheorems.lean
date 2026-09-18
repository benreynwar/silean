import PicoRV.Decoder.Internal.DecoderResolveStageVerification

/-! # Decoder resolve-stage theorems

This is the supported proof interface for the registered resolve stage. Its
aggregate child-register representation, schedules, and correspondence proof
remain under `Internal/`.
-/

namespace PicoRV.Decoder.ResolveStage

open Silean

section AllowedStep

variable {step : cycleContract.Step}
  (allowed : cycleContract.Allows step)

include allowed

/-- The visible decoder outputs are the contract's function of the current
inputs and the values held before the clock edge. -/
theorem outputs_of_allowed :
    step.outputs = outputValues (valuesOf step.inputs) step.currentState :=
  (outputRule_holds_iff step.inputs step.currentState step.outputs).mp
    (allowed.1 .outputs)

/-- The next registered decoder state is exactly the specified resolve-stage
transition. -/
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

end PicoRV.Decoder.ResolveStage
