import Silean.Modules.Equality.Internal.EqualityVerification

/-! Public equality declarations backed by the recursive implementation. -/

namespace Silean.Modules.Equality

open Silean
open Authoring.CircuitDescription

/-- Place structural equality under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Naming.SourceName)
    (left right : Net signalType) : Builder (Net .bit) := do
  let outputs ← ports.placeNamed signalType name (moduleStructure signalType)
    (Naming.naming signalType) left right
  pure outputs.result

/-- Place structural equality using the next conventional indexed name. -/
noncomputable def place (left right : Net signalType) : Builder (Net .bit) := do
  let outputs ← ports.placeIndexed signalType "equality"
    (moduleStructure signalType) (Naming.naming signalType) left right
  pure outputs.result

attribute [circuit_description] placeNamed place

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
  exact cycleContract.result signalType allowed

/-- The recursive equality hierarchy implements its exact cycle contract. -/
theorem implements_contract (signalType : SignalType) :
    Contracts.Cycle.Implements (moduleStructure signalType)
      (cycleContract signalType) (certification signalType).stateCorresponds :=
  (certification signalType).implements

end Silean.Modules.Equality
