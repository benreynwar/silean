import Silean.Modules.TupleField.Internal.TupleFieldVerification

/-! Public tuple-field declarations backed by generated internals. -/

namespace Silean.Modules.TupleField

open Silean
open Authoring.CircuitDescription

/-- Place a tuple-field selection with caller-supplied aggregate naming. -/
noncomputable def placeWith
    (signals : SignalMap) (field : signals.Label)
    (typeNaming : Naming.SignalTypeNaming signals.tupleType)
    (tuple : Net signals.tupleType) : Builder (Net (signals.signalType field)) := do
  let outputs ← ports.placeIndexed signals field "tuple_field"
    (moduleStructure signals field) (namingWith signals field typeNaming) tuple
  pure outputs.field

/-- Place a tuple-field selection using positional aggregate naming. -/
noncomputable def place (signals : SignalMap) (field : signals.Label)
    (tuple : Net signals.tupleType) : Builder (Net (signals.signalType field)) :=
  placeWith signals field (.positional signals.tupleType) tuple

attribute [circuit_description] placeWith place

/-- Every realizable step returns the field named by `field`. -/
theorem field_of_realization (signals : SignalMap) (field : signals.Label)
    {step : (moduleStructure signals field).Step}
    (realizes : (moduleStructure signals field).Realizes step) :
    step.outputs .field = selectedValue signals field (step.inputs .tuple) := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification signals field).hasCorrespondingState step.currentState
  obtain ⟨_, allowed, _⟩ :=
    (certification signals field).allows_of_realizes
      contractState step corresponds realizes
  exact cycleContract.field signals field allowed

/-- The generated hierarchy implements the exact selection contract. -/
theorem implements_contract (signals : SignalMap) (field : signals.Label) :
    Contracts.Cycle.Implements (moduleStructure signals field)
      (cycleContract signals field) (certification signals field).stateCorresponds :=
  (certification signals field).implements

end Silean.Modules.TupleField
