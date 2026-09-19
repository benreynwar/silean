import PicoRV.Control.Internal.ControlPhaseDecodeVerification
import PicoRV.Control.Internal.ControlPhaseDecodeCorrespondence

/-! # Control phase-decoder theorems -/

namespace PicoRV.Control.PhaseDecode

open Silean

namespace Description

open Silean.Naming Silean.Authoring.CircuitDescription

/-- The reader-facing phase comparisons elaborate to the certified typed
hierarchy with the same boundary, children, wiring, and names. -/
theorem authored_definition_corresponds :
    Corresponds description PhaseDecode.naming :=
  Internal.corresponds

end Description

theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs = outputValues step.inputs :=
  (outputRule_holds_iff step.inputs step.currentState step.outputs).mp
    (allowed.1 .apply)

theorem implements_contract :
    Silean.Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨certified.hasStructuralResult, certified.structuralResultUnique⟩

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end PicoRV.Control.PhaseDecode
