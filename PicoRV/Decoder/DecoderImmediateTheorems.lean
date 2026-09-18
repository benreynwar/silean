import PicoRV.Decoder.Internal.DecoderImmediateVerification

/-! # Immediate-decoder theorems

This is the supported proof interface for immediate decoding. The schedule and
child-level structural proof remain under `Internal/`.
-/

namespace PicoRV.Decoder.Immediate

open Silean

/-- Every contract-allowed step returns the immediate decoder's pure result. -/
theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs = outputValues (valuesOf step.inputs) :=
  (outputRule_holds_iff step.inputs step.currentState step.outputs).mp
    (allowed.1 .apply)

/-- Every realized structural step has the public immediate-decoder behavior. -/
theorem outputs_of_realizes {step : moduleStructure.Step}
    (realizes : moduleStructure.Realizes step) :
    step.outputs = outputValues (valuesOf step.inputs) := by
  rcases certified.hasCorrespondingState step.currentState with
    ⟨contractState, corresponds⟩
  rcases certified.implements contractState step corresponds realizes with
    ⟨_, allowed, _⟩
  exact outputs_of_allowed allowed

/-- The authored immediate-decoder hierarchy implements its cycle contract. -/
theorem implements_contract :
    Silean.Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

/-- The immediate-decoder hierarchy has exactly one structural solution. -/
theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨certified.hasStructuralResult, certified.structuralResultUnique⟩

/-- The immediate decoder and all descendants have concrete implementations. -/
theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end PicoRV.Decoder.Immediate
