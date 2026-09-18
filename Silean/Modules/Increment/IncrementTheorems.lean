import Silean.Modules.Increment.Internal.IncrementVerification

/-! # Incrementer theorems

This is the supported structural proof interface for the recursive incrementer.
Its hierarchy assignment and inductive certification are implementation details.
-/

namespace Silean.Modules.Increment

open Silean

/-- Every realizable incrementer step returns the mathematical increment. -/
theorem result_of_realization (width : Nat)
    {step : (moduleStructure width).Step}
    (realizes : (moduleStructure width).Realizes step) :
    step.outputs .result = incrementValue width (step.inputs .value) := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification width).hasCorrespondingState step.currentState
  obtain ⟨_, allowed, _⟩ := (certification width).allows_of_realizes
    contractState step corresponds realizes
  exact result_of_allowed width allowed

/-- The recursive incrementer implements its exact cycle contract. -/
theorem implements_contract (width : Nat) :
    Contracts.Cycle.Implements (moduleStructure width) (cycleContract width)
      (certification width).stateCorresponds :=
  (certification width).implements

end Silean.Modules.Increment
