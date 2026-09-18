import Silean.Modules.Equality.Internal.EqualityVerification

/-! # Equality theorems

The recursive hierarchy in `Equality.lean` implements its exact cycle
contract. Certification construction remains under `Internal/`; this file is
the public proof boundary for parents and checks. -/

namespace Silean.Modules.Equality

open Silean

/-- Every realizable boundary step reports whether its two inputs are equal. -/
theorem result_of_realization (signalType : SignalType)
    {step : (moduleStructure signalType).Step}
    (realizes : (moduleStructure signalType).Realizes step) :
    step.outputs .result =
      signalType.equal (step.inputs .left) (step.inputs .right) := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification signalType).hasCorrespondingState step.currentState
  obtain ⟨_, allowed, _⟩ := (certification signalType).allows_of_realizes
    contractState step corresponds realizes
  exact result_of_allowed signalType allowed

theorem certified_moduleStructure (signalType : SignalType) :
    (certified signalType).moduleStructure = moduleStructure signalType := rfl

theorem certified_cycleContract (signalType : SignalType) :
    (certified signalType).cycleContract = cycleContract signalType := rfl

/-- Structural equality implements its exact cycle contract. -/
theorem implements_contract (signalType : SignalType) :
    Contracts.Cycle.Implements (moduleStructure signalType)
      (cycleContract signalType) (certification signalType).stateCorresponds :=
  (certification signalType).implements

end Silean.Modules.Equality
