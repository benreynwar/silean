import PicoRV.Internal.DatapathVerification
import PicoRV.Datapath.DatapathNextTheorems

/-! # PicoRV datapath theorems

This is the supported proof interface for the registered datapath hierarchy.
The implementation schedule and child-level structural proof remain under
`Internal/`.
-/

namespace PicoRV.Datapath

open Silean

/-- The next registered state is the source-level datapath transition. -/
theorem nextState_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.nextState = nextState (inputsOfValues step.inputs) step.currentState :=
  allowed.2

/-- The authored datapath hierarchy implements its exact cycle contract. -/
theorem implements_contract :
    Silean.Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

/-- Structural equations for the complete datapath hierarchy have one
solution for every boundary input and physical state. -/
theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨certified.hasStructuralResult, certified.structuralResultUnique⟩

/-- The datapath hierarchy and all descendants are concrete. -/
theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end PicoRV.Datapath
