import Silean.Modules.ResetRegister.Internal.ResetRegisterVerification

/-! Public reset-register declarations backed by generated internals. -/

namespace Silean.Modules.ResetRegister

open Silean
open Authoring.CircuitDescription

/-- Place a reset register under a caller-chosen instance name and aggregate
naming. -/
noncomputable def placeNamedWith (name : Naming.SourceName)
    (typeNaming : Naming.SignalTypeNaming signalType)
    (resetValue : signalType.Denote) (value : Net signalType)
    (reset : Net .bit) : Builder (Net signalType) := do
  let outputs ← ports.placeNamed signalType name
    (moduleStructure signalType resetValue)
    (namingWith signalType resetValue typeNaming)
    value reset
  pure outputs.value

/-- Place a reset register under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Naming.SourceName)
    (resetValue : signalType.Denote) (value : Net signalType)
    (reset : Net .bit) : Builder (Net signalType) :=
  placeNamedWith name (.positional signalType) resetValue value reset

/-- Place a reset register with caller-supplied aggregate naming. -/
noncomputable def placeWith
    (typeNaming : Naming.SignalTypeNaming signalType)
    (resetValue : signalType.Denote) (value : Net signalType)
    (reset : Net .bit) : Builder (Net signalType) := do
  let outputs ← ports.placeIndexed signalType "reset_register"
    (moduleStructure signalType resetValue)
    (namingWith signalType resetValue typeNaming)
    value reset
  pure outputs.value

/-- Place a reset register using the next conventional indexed name. -/
noncomputable def place (resetValue : signalType.Denote)
    (value : Net signalType) (reset : Net .bit) : Builder (Net signalType) := do
  let outputs ← ports.placeIndexed signalType "reset_register"
    (moduleStructure signalType resetValue) (naming signalType resetValue)
    value reset
  pure outputs.value

attribute [circuit_description] placeNamedWith placeNamed placeWith place

/-- Every typed implementation corresponding to the authored construction
implements the reset-register contract. -/
theorem construction_correct (signalType : SignalType)
    (resetValue : signalType.Denote) :
    (description signalType resetValue).ImplementsCycleContract
      (cycleContract signalType resetValue) (Naming.ports signalType) :=
  Internal.construction_correct signalType resetValue

/-- The generated hierarchy implements the reset-register contract. -/
theorem implements_contract (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Contracts.Cycle.Implements
      (moduleStructure signalType resetValue)
      (cycleContract signalType resetValue)
      (certification signalType resetValue).stateCorresponds :=
  (certification signalType resetValue).implements

end Silean.Modules.ResetRegister
