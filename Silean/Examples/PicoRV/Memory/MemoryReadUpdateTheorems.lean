import Silean.Examples.PicoRV.Memory.Internal.MemoryReadUpdateVerification

/-! # Memory Read Update theorems

Supported verification boundary for the authored module. Structural schedules and
witness construction remain under the Internal directory.
-/

namespace Silean.Examples.PicoRV.Memory.ReadUpdate

open Silean

theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs .state =
      stateMap.pack (StateUpdate.outputState (readNextState) step.inputs) :=
  (StateUpdate.outputRule_holds_iff (readNextState)
    step.inputs step.currentState step.outputs).mp (allowed.1 .apply)


theorem implements_contract :
    Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨certified.hasStructuralResult, certified.structuralResultUnique⟩

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.Memory.ReadUpdate
