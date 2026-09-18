import Silean.Modules.VectorLayout.Internal.VectorLayoutVerification

/-! # Vector-layout theorems

This is the supported proof interface for fixed bit permutation, duplication,
selection, and constant insertion. Adapter wiring and scheduling remain
internal.
-/

namespace Silean.Modules.VectorLayout

open Silean

/-- Every realizable boundary step applies the declared bit layout. -/
theorem output_of_realization (inputWidth outputWidth : Nat)
    (layout : Fin outputWidth → BitSource inputWidth)
    {step : (moduleStructure inputWidth outputWidth layout).Step}
    (realizes : (moduleStructure inputWidth outputWidth layout).Realizes step) :
    step.outputs .output = VectorLayout.apply layout (step.inputs .input) := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification inputWidth outputWidth layout).hasCorrespondingState
      step.currentState
  obtain ⟨_, allowed, _⟩ :=
    (certification inputWidth outputWidth layout).allows_of_realizes
      contractState step corresponds realizes
  exact output_of_allowed inputWidth outputWidth layout allowed

/-- The layout hierarchy implements its exact cycle contract. -/
theorem implements_contract (inputWidth outputWidth : Nat)
    (layout : Fin outputWidth → BitSource inputWidth) :
    Contracts.Cycle.Implements (moduleStructure inputWidth outputWidth layout)
      (cycleContract inputWidth outputWidth layout)
      (certification inputWidth outputWidth layout).stateCorresponds :=
  (certification inputWidth outputWidth layout).implements

end Silean.Modules.VectorLayout
