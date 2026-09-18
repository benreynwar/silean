import Silean.Modules.Add.Internal.AddVerification

/-! # Adder theorems

This is the supported structural proof interface for the recursive adder.
Schedules and the inductive certification remain implementation details.
-/

namespace Silean.Modules.Add

open Silean

/-- Every realizable adder step has the complete arithmetic behavior specified
by its cycle contract. -/
theorem behavior_of_realization (width : Nat)
    {step : (moduleStructure width).Step}
    (realizes : (moduleStructure width).Realizes step) :
    Behavior width step.inputs step.outputs := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification width).hasCorrespondingState step.currentState
  obtain ⟨_, allowed, _⟩ := (certification width).allows_of_realizes
    contractState step corresponds realizes
  exact Behavior.of_allowed width allowed

/-- The recursive adder implements its exact cycle contract. -/
theorem implements_contract (width : Nat) :
    Contracts.Cycle.Implements (moduleStructure width) (cycleContract width)
      (certification width).stateCorresponds :=
  (certification width).implements

end Silean.Modules.Add
