import PicoRV.Memory.Internal.MemoryResponseVerification
import PicoRV.Memory.Internal.MemoryResponseCorrespondence

/-! # Memory Response theorems

Supported verification boundary for the authored module. Structural schedules and
witness construction remain under the Internal directory.
-/

namespace PicoRV.Memory.Response

open Silean

/-- The concise authored definition expands to the production hierarchy. -/
theorem authored_definition_corresponds :
    Silean.Authoring.CircuitDescription.Corresponds
      Description.description naming :=
  Description.Internal.corresponds

/-- Completion and response data exposed by an allowed boundary step. -/
theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs .mem_done = doneValue
        (step.inputs .resetn) (step.inputs .mem_do_rinst)
        (step.inputs .mem_do_rdata) (step.inputs .mem_do_wdata)
        (step.inputs .mem_ready) (step.inputs .current) ∧
      step.outputs .mem_rdata_latched = memRdataLatchedFrom
        (step.inputs .mem_ready) (step.inputs .mem_rdata)
        (stateMap.unpack (step.inputs .current)) := by
  exact ⟨(doneRule_holds_iff _ _ _).mp (allowed.1 .done),
    (dataRule_holds_iff _ _ _).mp (allowed.1 .data)⟩

theorem implements_contract :
    Silean.Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨certified.hasStructuralResult, certified.structuralResultUnique⟩

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end PicoRV.Memory.Response
