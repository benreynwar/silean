import PicoRV.Decoder.Internal.DecoderInstructionFieldsVerification

/-! # Instruction-field theorems

This is the supported proof interface for the shared instruction-field
predicates. Layout and child-level certification details remain internal.
-/

namespace PicoRV.Decoder.InstructionFields.Structure

open Silean

/-- An allowed step exposes exactly the predicates decoded from `word`. -/
theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs = outputValues (step.inputs .word) :=
  (outputRule_holds_iff step.inputs step.currentState step.outputs).mp
    (allowed.1 .apply)

/-- Every realized structural step has the public field-decoding behavior. -/
theorem outputs_of_realizes {step : moduleStructure.Step}
    (realizes : moduleStructure.Realizes step) :
    step.outputs = outputValues (step.inputs .word) := by
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

end PicoRV.Decoder.InstructionFields.Structure
