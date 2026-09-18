import Silean.Modules.TupleField.Internal.TupleFieldVerification

/-! # Tuple-field theorems

This is the supported proof interface for selecting one typed field from a
named tuple. Positional splitter wiring and scheduling remain internal.
-/

namespace Silean.Modules.TupleField

open Silean

/-- Every realizable boundary step returns the field named by `field`. -/
theorem field_of_realization (signals : SignalMap) (field : signals.Label)
    {step : (moduleStructure signals field).Step}
    (realizes : (moduleStructure signals field).Realizes step) :
    step.outputs .field = selectedValue signals field (step.inputs .tuple) := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification signals field).hasCorrespondingState step.currentState
  obtain ⟨_, allowed, _⟩ :=
    (certification signals field).allows_of_realizes
      contractState step corresponds realizes
  exact field_of_allowed signals field allowed

/-- The tuple-field hierarchy implements its exact selection contract. -/
theorem implements_contract (signals : SignalMap) (field : signals.Label) :
    Contracts.Cycle.Implements (moduleStructure signals field)
      (cycleContract signals field) (certification signals field).stateCorresponds :=
  (certification signals field).implements

end Silean.Modules.TupleField
