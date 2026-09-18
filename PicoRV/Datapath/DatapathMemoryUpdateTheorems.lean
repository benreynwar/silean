import PicoRV.Datapath.Internal.DatapathMemoryUpdateVerification

/-! # Datapath memory-update theorems

Supported verification boundaries for the shared memory-update core and its
load/store specializations. Structural proof details remain under `Internal/`.
-/

namespace PicoRV.Datapath

open Silean

namespace MemoryUpdateCore

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

end MemoryUpdateCore

namespace StoreUpdate

theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs .state = stateMap.pack
      (StateUpdate.outputState (memoryNextState false) step.inputs) :=
  (StateUpdate.outputRule_holds_iff (memoryNextState false)
    step.inputs step.currentState step.outputs).mp (allowed.1 .apply)

theorem implements_contract :
    Silean.Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨certified.hasStructuralResult, certified.structuralResultUnique⟩

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end StoreUpdate

namespace LoadUpdate

theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs .state = stateMap.pack
      (StateUpdate.outputState (memoryNextState true) step.inputs) :=
  (StateUpdate.outputRule_holds_iff (memoryNextState true)
    step.inputs step.currentState step.outputs).mp (allowed.1 .apply)

theorem implements_contract :
    Silean.Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨certified.hasStructuralResult, certified.structuralResultUnique⟩

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end LoadUpdate

end PicoRV.Datapath
