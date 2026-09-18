import Silean.Modules.VectorConcat.Internal.VectorConcatVerification

/-! # Vector-concatenation theorems

This is the supported proof interface for vector concatenation. Splitter and
combiner wiring and the proof schedule remain internal.
-/

namespace Silean.Modules.VectorConcat

open Silean

/-- Every realizable boundary step concatenates the two input vectors. -/
theorem result_of_realization (element : SignalType) (leftWidth rightWidth : Nat)
    {step : (moduleStructure element leftWidth rightWidth).Step}
    (realizes : (moduleStructure element leftWidth rightWidth).Realizes step) :
    step.outputs .result = concat (step.inputs .left) (step.inputs .right) := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification element leftWidth rightWidth).hasCorrespondingState
      step.currentState
  obtain ⟨_, allowed, _⟩ :=
    (certification element leftWidth rightWidth).allows_of_realizes
      contractState step corresponds realizes
  exact result_of_allowed element leftWidth rightWidth allowed

/-- The concatenation hierarchy implements its exact cycle contract. -/
theorem implements_contract (element : SignalType) (leftWidth rightWidth : Nat) :
    Contracts.Cycle.Implements (moduleStructure element leftWidth rightWidth)
      (cycleContract element leftWidth rightWidth)
      (certification element leftWidth rightWidth).stateCorresponds :=
  (certification element leftWidth rightWidth).implements

end Silean.Modules.VectorConcat
