import PicoRV.Internal.ControlVerification
import PicoRV.Control.ControlNextTheorems

/-! # PicoRV control theorems

This is the supported proof interface for the registered control hierarchy.
The implementation schedule and child-level structural proof remain under
`Internal/`.
-/

namespace PicoRV.Control

open Silean

/-- A contract-allowed cycle exposes the pre-edge control state. -/
theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs = outputValues step.currentState :=
  (outputRule_holds_iff step.inputs step.currentState step.outputs).mp
    (allowed.1 .outputs)

/-- The next registered state is the source-level control transition. -/
theorem nextState_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.nextState = nextState (inputsOfValues step.inputs) step.currentState :=
  allowed.2

/-- The authored control hierarchy implements its exact cycle contract. -/
theorem implements_contract :
    Silean.Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

/-- Structural equations for the complete control hierarchy have one solution
for every boundary input and physical state. -/
theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨certified.hasStructuralResult, certified.structuralResultUnique⟩

/-- The control hierarchy and all descendants are concrete. -/
theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end PicoRV.Control
