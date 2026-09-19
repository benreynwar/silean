import Silean.Modules.EqualsConstant.Internal.EqualsConstantVerification

/-! # EqualsConstant theorems

The authored constant-comparison circuit implements the exact contract in
`EqualsConstant.lean`. Structural clients should use the boundary theorem
below rather than the internal hierarchy witness. -/

namespace Silean.Modules.EqualsConstant

open Silean

namespace Description

open Naming Authoring.CircuitDescription

/-- The reader-facing constant-comparison circuit elaborates to the certified
typed hierarchy with the same boundary, children, wiring, and names. -/
theorem authored_definition_corresponds (signalType : SignalType)
    (constant : signalType.Denote) :
    Corresponds (description signalType constant)
      (EqualsConstant.naming signalType constant) :=
  Internal.corresponds signalType constant

end Description

/-- Every realizable boundary step compares the input with the fixed value. -/
theorem result_of_realization (signalType : SignalType)
    (constant : signalType.Denote)
    {step : (moduleStructure signalType constant).Step}
    (realizes : (moduleStructure signalType constant).Realizes step) :
    step.outputs .result = signalType.equal (step.inputs .value) constant := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification signalType constant).hasCorrespondingState step.currentState
  obtain ⟨_, allowed, _⟩ :=
    (certification signalType constant).allows_of_realizes
      contractState step corresponds realizes
  exact result_of_allowed signalType constant allowed

/-- The structural circuit implements its exact comparison contract. -/
theorem implements_contract (signalType : SignalType)
    (constant : signalType.Denote) :
    Contracts.Cycle.Implements (moduleStructure signalType constant)
      (cycleContract signalType constant)
      (certification signalType constant).stateCorresponds :=
  (certification signalType constant).implements

end Silean.Modules.EqualsConstant
