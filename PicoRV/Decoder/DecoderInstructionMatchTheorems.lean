import PicoRV.Decoder.Internal.DecoderInstructionMatchVerification

/-! # Instruction-match theorems

This is the supported proof interface for exact instruction matching. The
shared field decoder, match gates, reduction trees, and structural
certification remain under `Internal/`.
-/

namespace PicoRV.Decoder.InstructionMatch.Structure

open Silean

/-- Every allowed step produces exactly the instruction-match outputs. -/
theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs = outputValues (valuesOf step.inputs) :=
  (outputRule_holds_iff step.inputs step.currentState step.outputs).mp
    (allowed.1 .apply)

/-- Every realized structural step has the public instruction-match behavior. -/
theorem outputs_of_realizes {step : moduleStructure.Step}
    (realizes : moduleStructure.Realizes step) :
    step.outputs = outputValues (valuesOf step.inputs) := by
  rcases certified.hasCorrespondingState step.currentState with
    ⟨contractState, corresponds⟩
  rcases certified.implements contractState step corresponds realizes with
    ⟨_, allowed, _⟩
  exact outputs_of_allowed allowed

theorem implements_contract :
    Silean.Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨certified.hasStructuralResult, certified.structuralResultUnique⟩

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end PicoRV.Decoder.InstructionMatch.Structure
