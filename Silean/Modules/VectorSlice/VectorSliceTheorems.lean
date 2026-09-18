import Silean.Modules.VectorSlice.Internal.VectorSliceVerification

/-! # Vector-slice theorems

This is the supported proof interface for selecting a contiguous vector
range. Splitter/combiner wiring and scheduling remain internal.
-/

namespace Silean.Modules.VectorSlice

open Silean

/-- Every realizable boundary step returns the requested contiguous range. -/
theorem result_of_realization (element : SignalType)
    (prefixWidth width suffixWidth : Nat)
    {step : (moduleStructure element prefixWidth width suffixWidth).Step}
    (realizes :
      (moduleStructure element prefixWidth width suffixWidth).Realizes step) :
    step.outputs .result = slice (step.inputs .value) := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification element prefixWidth width suffixWidth).hasCorrespondingState
      step.currentState
  obtain ⟨_, allowed, _⟩ :=
    (certification element prefixWidth width suffixWidth).allows_of_realizes
      contractState step corresponds realizes
  exact result_of_allowed element prefixWidth width suffixWidth allowed

/-- The slice hierarchy implements its exact cycle contract. -/
theorem implements_contract (element : SignalType)
    (prefixWidth width suffixWidth : Nat) :
    Contracts.Cycle.Implements
      (moduleStructure element prefixWidth width suffixWidth)
      (cycleContract element prefixWidth width suffixWidth)
      (certification element prefixWidth width suffixWidth).stateCorresponds :=
  (certification element prefixWidth width suffixWidth).implements

end Silean.Modules.VectorSlice
