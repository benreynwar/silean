import PicoRV.Control.Internal.ControlCommandFinishVerification
import PicoRV.Control.Internal.ControlCommandFinishCorrespondence

/-! # Control command-finishing theorems -/

namespace PicoRV.Control.CommandFinish

open Silean

/-- The concise authored definition and expanded typed hierarchy describe the
same ports, children, wiring, and emitted names. -/
theorem authored_definition_corresponds :
    Silean.Authoring.CircuitDescription.Corresponds
      Description.description naming :=
  Description.Internal.corresponds

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

end PicoRV.Control.CommandFinish
