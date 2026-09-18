import Silean.Examples.PicoRV.Internal.MemoryVerification
import Silean.Examples.PicoRV.Memory.MemoryNextTheorems

/-! # PicoRV memory-interface theorems

This is the supported proof interface for the registered memory hierarchy.
The implementation schedule and child-level structural proof remain under
`Internal/`.
-/

namespace Silean.Examples.PicoRV.Memory

open Silean

/-- The next registered state is the source-level memory transition. -/
theorem nextState_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.nextState = nextState (inputsOfValues step.inputs) step.currentState :=
  allowed.2

/-- The authored memory hierarchy implements its exact cycle contract. -/
theorem implements_contract :
    Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

/-- Structural equations for the complete memory hierarchy have one solution
for every boundary input and physical state. -/
theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨certified.hasStructuralResult, certified.structuralResultUnique⟩

/-- The memory hierarchy and all descendants are concrete. -/
theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.Memory
