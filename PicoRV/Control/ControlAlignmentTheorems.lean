import PicoRV.Control.Internal.ControlAlignmentVerification
import PicoRV.Control.Internal.ControlAlignmentCorrespondence

/-! # Control alignment theorems

Supported boundary behavior for alignment detection. Proof construction remains
under Internal.
-/

namespace PicoRV.Control.Alignment

open Silean

/-- The concise authored definition and expanded typed hierarchy describe the
same ports, children, wiring, and emitted names. -/
theorem authored_definition_corresponds :
    Silean.Authoring.CircuitDescription.Corresponds
      Description.description naming :=
  Description.Internal.corresponds

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

end PicoRV.Control.Alignment
