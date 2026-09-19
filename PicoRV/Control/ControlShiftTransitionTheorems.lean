import PicoRV.Control.Internal.ControlShiftTransitionVerification
import PicoRV.Control.Internal.ControlShiftTransitionCorrespondence

/-! # Shift Transition theorems

This is the supported proof interface. The structural hierarchy, rule schedule,
and certification witness remain under Internal.
-/

namespace PicoRV.Control.ShiftTransition

open Silean

/-- The concise authored definition and expanded typed hierarchy describe the
same ports, children, wiring, and emitted names. -/
theorem authored_definition_corresponds :
    Silean.Authoring.CircuitDescription.Corresponds
      Description.description naming :=
  Description.Internal.corresponds

/-- Every contract-allowed step returns the source-level transition. -/
theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs .transition =
      ((fun inputs _ updated => shiftTransition inputs updated) (Inputs.unpack (step.inputs .inputs))
        (stateMap.unpack (step.inputs .current))
        (stateMap.unpack (step.inputs .updated))).pack :=
  (PhaseTransition.outputRule_holds_iff (fun inputs _ updated => shiftTransition inputs updated)
    step.inputs step.currentState step.outputs).mp (allowed.1 .apply)

/-- The authored hierarchy implements its exact cycle contract. -/
theorem implements_contract :
    Silean.Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

/-- The hierarchy has exactly one structural solution. -/
theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨certified.hasStructuralResult, certified.structuralResultUnique⟩

/-- The hierarchy contains no behavioral blackboxes. -/
theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end PicoRV.Control.ShiftTransition
