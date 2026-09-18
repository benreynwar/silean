import Silean.Examples.PicoRV.Control.Internal.ControlNextVerification
import Silean.Examples.PicoRV.Control.ControlAlignmentTheorems
import Silean.Examples.PicoRV.Control.ControlBaselineTheorems
import Silean.Examples.PicoRV.Control.ControlCommandFinishTheorems
import Silean.Examples.PicoRV.Control.ControlExecuteTransitionTheorems
import Silean.Examples.PicoRV.Control.ControlFetchTransitionTheorems
import Silean.Examples.PicoRV.Control.ControlLoadRs1TransitionTheorems
import Silean.Examples.PicoRV.Control.ControlLoadRs2TransitionTheorems
import Silean.Examples.PicoRV.Control.ControlLoadTransitionTheorems
import Silean.Examples.PicoRV.Control.ControlPhaseDecodeTheorems
import Silean.Examples.PicoRV.Control.ControlResetAndAlignmentOverrideTheorems
import Silean.Examples.PicoRV.Control.ControlShiftTransitionTheorems
import Silean.Examples.PicoRV.Control.ControlStoreTransitionTheorems
import Silean.Examples.PicoRV.Control.ControlTrapTransitionTheorems

/-! # Control next-state theorems

This is the supported proof interface for the combinational next-state
hierarchy. Its phase children, schedule, and structural proof remain internal.
-/

namespace Silean.Examples.PicoRV.Control.ControlNext

open Silean

theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs .state = stateMap.pack (outputState step.inputs) :=
  (outputRule_holds_iff step.inputs step.currentState step.outputs).mp
    (allowed.1 .apply)

theorem implements_contract :
    Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨certified.hasStructuralResult, certified.structuralResultUnique⟩

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.Control.ControlNext
