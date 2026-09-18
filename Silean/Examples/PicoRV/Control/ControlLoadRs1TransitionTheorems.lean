import Silean.Examples.PicoRV.Control.Internal.ControlLoadRs1TransitionVerification

/-! # Load Rs1Transition theorems

This is the supported proof interface. The structural hierarchy, rule schedule,
and certification witness remain under Internal.
-/

namespace Silean.Examples.PicoRV.Control.LoadRs1Transition

open Silean

/-- Every contract-allowed step returns the source-level transition. -/
theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs .transition =
      ((fun inputs _ updated => loadRs1Transition inputs updated) (Inputs.unpack (step.inputs .inputs))
        (stateMap.unpack (step.inputs .current))
        (stateMap.unpack (step.inputs .updated))).pack :=
  (PhaseTransition.outputRule_holds_iff (fun inputs _ updated => loadRs1Transition inputs updated)
    step.inputs step.currentState step.outputs).mp (allowed.1 .apply)

/-- The authored hierarchy implements its exact cycle contract. -/
theorem implements_contract :
    Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

/-- The hierarchy has exactly one structural solution. -/
theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨certified.hasStructuralResult, certified.structuralResultUnique⟩

/-- The hierarchy contains no behavioral blackboxes. -/
theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.Control.LoadRs1Transition
