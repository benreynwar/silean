import PicoRV.Datapath.Internal.DatapathLoadRs2UpdateVerification
import PicoRV.Datapath.Internal.DatapathLoadRs2UpdateCorrespondence

/-! # Datapath Load Rs2Update theorems

Supported verification boundary for the authored module. Structural schedules and
witness construction remain under the Internal directory.
-/

namespace PicoRV.Datapath.LoadRs2Update

open Silean

/-- The concise authored definition expands to the production hierarchy. -/
theorem authored_definition_corresponds :
    Silean.Authoring.CircuitDescription.Corresponds
      Description.description naming :=
  Description.Internal.corresponds

theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs .state =
      stateMap.pack (StateUpdate.outputState (fun inputs _ updated => loadRs2NextState inputs updated) step.inputs) :=
  (StateUpdate.outputRule_holds_iff (fun inputs _ updated => loadRs2NextState inputs updated)
    step.inputs step.currentState step.outputs).mp (allowed.1 .apply)


theorem implements_contract :
    Silean.Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨certified.hasStructuralResult, certified.structuralResultUnique⟩

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end PicoRV.Datapath.LoadRs2Update
