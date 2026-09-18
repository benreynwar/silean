import Silean.Modules.VectorSplit.Internal.VectorSplitVerification

/-! # Vector-split theorems

This is the supported proof interface for splitting a vector at a fixed
boundary. Positional adapter wiring and scheduling remain internal.
-/

namespace Silean.Modules.VectorSplit

open Silean

/-- Every realizable boundary step returns the two portions of its input. -/
theorem outputs_of_realization (element : SignalType) (leftWidth rightWidth : Nat)
    {step : (moduleStructure element leftWidth rightWidth).Step}
    (realizes : (moduleStructure element leftWidth rightWidth).Realizes step) :
    step.outputs .left = leftPart (step.inputs .value) ∧
      step.outputs .right = rightPart (step.inputs .value) := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification element leftWidth rightWidth).hasCorrespondingState
      step.currentState
  obtain ⟨_, allowed, _⟩ :=
    (certification element leftWidth rightWidth).allows_of_realizes
      contractState step corresponds realizes
  exact outputs_of_allowed element leftWidth rightWidth allowed

/-- The split hierarchy implements its exact cycle contract. -/
theorem implements_contract (element : SignalType) (leftWidth rightWidth : Nat) :
    Contracts.Cycle.Implements (moduleStructure element leftWidth rightWidth)
      (cycleContract element leftWidth rightWidth)
      (certification element leftWidth rightWidth).stateCorresponds :=
  (certification element leftWidth rightWidth).implements

end Silean.Modules.VectorSplit
