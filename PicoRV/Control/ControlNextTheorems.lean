import PicoRV.Control.Internal.ControlNextVerification
import PicoRV.Control.Internal.ControlNextCorrespondence
import PicoRV.Control.ControlAlignmentTheorems
import PicoRV.Control.ControlBaselineTheorems
import PicoRV.Control.ControlCommandFinishTheorems
import PicoRV.Control.ControlExecuteTransitionTheorems
import PicoRV.Control.ControlFetchTransitionTheorems
import PicoRV.Control.ControlLoadRs1TransitionTheorems
import PicoRV.Control.ControlLoadRs2TransitionTheorems
import PicoRV.Control.ControlLoadTransitionTheorems
import PicoRV.Control.ControlPhaseDecodeTheorems
import PicoRV.Control.ControlResetAndAlignmentOverrideTheorems
import PicoRV.Control.ControlShiftTransitionTheorems
import PicoRV.Control.ControlStoreTransitionTheorems
import PicoRV.Control.ControlTrapTransitionTheorems

/-! # Control next-state theorems

This is the supported proof interface for the combinational next-state
hierarchy. Its phase children, schedule, and structural proof remain internal.
-/

namespace PicoRV.Control.ControlNext

/-- The concise authored definition expands to the production hierarchy. -/
theorem authored_definition_corresponds :
    Silean.Authoring.CircuitDescription.Corresponds
      Description.description naming :=
  Description.Internal.corresponds

open Silean

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

end PicoRV.Control.ControlNext
