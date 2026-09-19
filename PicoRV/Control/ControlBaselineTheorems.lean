import PicoRV.Control.Internal.ControlBaselineVerification
import PicoRV.Control.Internal.ControlBaselineCorrespondence

/-! # Control baseline theorems -/

namespace PicoRV.Control.Baseline

open Silean

namespace Description

open Silean.Naming Silean.Authoring.CircuitDescription

/-- The reader-facing baseline circuit elaborates to the certified typed
hierarchy with the same named aggregate boundary and feedback-free wiring. -/
theorem authored_definition_corresponds :
    Corresponds description Baseline.naming :=
  Internal.corresponds

end Description

theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs .state = stateMap.pack (outputState step.inputs) :=
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

end PicoRV.Control.Baseline
