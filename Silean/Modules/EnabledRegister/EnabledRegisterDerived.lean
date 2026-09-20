import Silean.Modules.EnabledRegister.Internal.EnabledRegisterVerification

/-! Public enabled-register declarations backed by generated internals. -/

namespace Silean.Modules.EnabledRegister

open Silean
open Authoring.CircuitDescription

/-- Place an enabled register under a caller-chosen instance name and
aggregate naming. -/
noncomputable def placeNamedWith (name : Naming.SourceName)
    (typeNaming : Naming.SignalTypeNaming signalType)
    (data : Net signalType) (enable : Net .bit) : Builder (Net signalType) := do
  let outputs ← ports.placeNamed signalType name
    (moduleStructure signalType) (namingWith signalType typeNaming)
    data enable
  pure outputs.q

/-- Place an enabled register under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Naming.SourceName)
    (data : Net signalType) (enable : Net .bit) : Builder (Net signalType) :=
  placeNamedWith name (.positional signalType) data enable

/-- Place an enabled register with caller-supplied aggregate naming. -/
noncomputable def placeWith
    (typeNaming : Naming.SignalTypeNaming signalType)
    (data : Net signalType) (enable : Net .bit) : Builder (Net signalType) := do
  let outputs ← ports.placeIndexed signalType "enabled_register"
    (moduleStructure signalType) (namingWith signalType typeNaming)
    data enable
  pure outputs.q

/-- Place an enabled register using the next conventional indexed name. -/
noncomputable def place (data : Net signalType)
    (enable : Net .bit) : Builder (Net signalType) := do
  let outputs ← ports.placeIndexed signalType "enabled_register"
    (moduleStructure signalType) (naming signalType)
    data enable
  pure outputs.q

attribute [circuit_description] placeNamedWith placeNamed placeWith place

/-- Every typed implementation corresponding to the authored construction
implements the enabled-register contract. -/
theorem construction_correct (signalType : SignalType) :
    (description signalType).ImplementsCycleContract
      (cycleContract signalType) (Naming.ports signalType) :=
  Internal.construction_correct signalType

/-- The generated hierarchy implements the enabled-register contract. -/
theorem implements_contract (signalType : SignalType) :
    Contracts.Cycle.Implements
      (moduleStructure signalType)
      (cycleContract signalType)
      (certification signalType).stateCorresponds :=
  (certification signalType).implements

end Silean.Modules.EnabledRegister
