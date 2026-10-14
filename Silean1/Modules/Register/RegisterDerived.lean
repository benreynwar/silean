import Silean.Authoring.CircuitDescription
import Silean.Modules.Register.Internal.RegisterVerification

/-! Public register declarations backed by the recursive implementation. -/

namespace Silean.Modules.Register

open Silean.Authoring.CircuitDescription

/-- Place a register under a caller-chosen instance name and aggregate naming. -/
noncomputable def placeNamedWith (name : Silean.Naming.SourceName)
    (typeNaming : Silean.Naming.SignalTypeNaming signalType)
    (value : Net signalType) : Builder (Net signalType) := do
  let child ← Authoring.CircuitDescription.placeNamed name
    (designWith typeNaming) fun | .input => value
  pure (child .output)

/-- Place a register under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Silean.Naming.SourceName)
    (value : Net signalType) : Builder (Net signalType) :=
  placeNamedWith name (.positional signalType) value

/-- Place a register with caller-supplied aggregate naming. -/
noncomputable def placeWith
    (typeNaming : Silean.Naming.SignalTypeNaming signalType)
    (value : Net signalType) : Builder (Net signalType) := do
  let child ← placeIndexed "register" (designWith typeNaming) fun
    | .input => value
  pure (child .output)

/-- Place a register using the next conventional indexed name. -/
noncomputable def place (value : Net signalType) : Builder (Net signalType) := do
  let child ← placeIndexed "register" (design signalType) fun
    | .input => value
  pure (child .output)

attribute [circuit_description] placeNamedWith placeNamed placeWith place

/-- The recursive register implementation satisfies its cycle contract. -/
theorem implements_contract (signalType : Silean.SignalType) :
    Silean.Contracts.Cycle.Implements
      (moduleStructure signalType)
      (cycleContract signalType)
      (certification signalType).stateCorresponds :=
  (certification signalType).implements

theorem certified_moduleStructure (signalType : Silean.SignalType) :
    (certified signalType).moduleStructure = moduleStructure signalType :=
  rfl

end Silean.Modules.Register
