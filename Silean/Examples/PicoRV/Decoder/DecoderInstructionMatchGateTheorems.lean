import Silean.Examples.PicoRV.Decoder.Internal.DecoderInstructionMatchGateVerification

/-! # Instruction-match gate theorems

This is the supported proof interface for the reusable three-condition match
gate. Its two-gate structural proof remains under `Internal/`.
-/

namespace Silean.Examples.PicoRV.Decoder.InstructionMatch.MatchGate.Structure

open Silean

/-- An allowed match-gate step returns the conjunction of all conditions. -/
theorem result_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs .result =
      ((step.inputs .broad && step.inputs .field) && step.inputs .qualifier) :=
  (outputRule_holds_iff step.inputs step.currentState step.outputs).mp
    (allowed.1 .apply)

/-- Every realized structural step has the public match-gate behavior. -/
theorem result_of_realizes {step : moduleStructure.Step}
    (realizes : moduleStructure.Realizes step) :
    step.outputs .result =
      ((step.inputs .broad && step.inputs .field) && step.inputs .qualifier) := by
  rcases certified.hasCorrespondingState step.currentState with
    ⟨contractState, corresponds⟩
  rcases certified.implements contractState step corresponds realizes with
    ⟨_, allowed, _⟩
  exact result_of_allowed allowed

theorem implements_contract :
    Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨certified.hasStructuralResult, certified.structuralResultUnique⟩

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.Decoder.InstructionMatch.MatchGate.Structure
