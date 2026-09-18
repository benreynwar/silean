import Silean.Modules.BinaryToOneHot.Internal.BinaryToOneHotVerification

/-! # Binary-to-one-hot theorems

The recursive decoder hierarchy in `BinaryToOneHot.lean` implements its exact
cycle contract. Its schedules and inductive certification remain internal. -/

namespace Silean.Modules.BinaryToOneHot

open Silean

/-- Every realizable boundary step produces the one-hot decoding of its input. -/
theorem result_of_realization (width : Nat)
    {step : (moduleStructure width).Step}
    (realizes : (moduleStructure width).Realizes step) :
    step.outputs .result = oneHot width (step.inputs .value) := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification width).hasCorrespondingState step.currentState
  obtain ⟨_, allowed, _⟩ := (certification width).allows_of_realizes
    contractState step corresponds realizes
  exact (outputRule_holds_iff width step.inputs contractState step.outputs).mp
    (allowed.1 .apply)

theorem certified_moduleStructure (width : Nat) :
    (certified width).moduleStructure = moduleStructure width := rfl

theorem certified_cycleContract (width : Nat) :
    (certified width).cycleContract = cycleContract width := rfl

/-- The structural decoder implements its exact one-hot cycle contract. -/
theorem implements_contract (width : Nat) :
    Contracts.Cycle.Implements (moduleStructure width) (cycleContract width)
      (certification width).stateCorresponds :=
  (certification width).implements

end Silean.Modules.BinaryToOneHot
