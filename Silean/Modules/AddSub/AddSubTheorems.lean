import Silean.Modules.AddSub.Internal.AddSubVerification

/-! # Add/subtract theorems

This is the supported structural proof interface for the add/subtract unit.
Child schedules and hierarchy witnesses remain internal verification details.
-/

namespace Silean.Modules.AddSub

open Silean

namespace Description

open Naming Authoring.CircuitDescription

/-- The reader-facing add/subtract circuit elaborates to the certified typed
hierarchy with the same boundary, children, wiring, and names. -/
theorem authored_definition_corresponds (width : Nat) :
    Corresponds (description width) (AddSub.naming width) :=
  Internal.corresponds width

end Description

/-- Every realizable add/subtract step has the complete behavior selected by
its `subtract` input. -/
theorem behavior_of_realization (width : Nat)
    {step : (moduleStructure width).Step}
    (realizes : (moduleStructure width).Realizes step) :
    Behavior width step.inputs step.outputs := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification width).hasCorrespondingState step.currentState
  obtain ⟨_, allowed, _⟩ := (certification width).allows_of_realizes
    contractState step corresponds realizes
  exact Behavior.of_allowed width allowed

/-- The structural add/subtract unit implements its exact cycle contract. -/
theorem implements_contract (width : Nat) :
    Contracts.Cycle.Implements (moduleStructure width) (cycleContract width)
      (certification width).stateCorresponds :=
  (certification width).implements

end Silean.Modules.AddSub
