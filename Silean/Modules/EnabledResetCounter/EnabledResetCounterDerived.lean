import Silean.Modules.EnabledResetCounter.Internal.EnabledResetCounterVerification

/-! Public enabled-reset-counter declarations backed by generated internals. -/

namespace Silean.Modules.EnabledResetCounter

open Silean
open Authoring.CircuitDescription

/-- Place a counter under a caller-chosen instance name and aggregate naming. -/
noncomputable def placeNamedWith (name : Naming.SourceName)
    (typeNaming : Naming.SignalTypeNaming (valueType width))
    (resetValue : Value width) (enable reset : Net .bit) :
    Builder (Net (valueType width)) := do
  let outputs ← ports.placeNamed width name
    (moduleStructure width resetValue)
    (namingWith width resetValue typeNaming)
    enable reset
  pure outputs.value

/-- Place a counter under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Naming.SourceName)
    (resetValue : Value width) (enable reset : Net .bit) :
    Builder (Net (valueType width)) :=
  placeNamedWith name (.positional (valueType width))
    resetValue enable reset

/-- Place a counter with caller-supplied aggregate naming. -/
noncomputable def placeWith
    (typeNaming : Naming.SignalTypeNaming (valueType width))
    (resetValue : Value width) (enable reset : Net .bit) :
    Builder (Net (valueType width)) := do
  let outputs ← ports.placeIndexed width "enabled_reset_counter"
    (moduleStructure width resetValue)
    (namingWith width resetValue typeNaming)
    enable reset
  pure outputs.value

/-- Place a counter using the next conventional indexed name. -/
noncomputable def place (resetValue : Value width)
    (enable reset : Net .bit) : Builder (Net (valueType width)) := do
  let outputs ← ports.placeIndexed width "enabled_reset_counter"
    (moduleStructure width resetValue) (naming width resetValue)
    enable reset
  pure outputs.value

attribute [circuit_description] placeNamedWith placeNamed placeWith place

/-- Every typed implementation corresponding to the authored construction
implements the enabled-reset-counter contract. -/
theorem construction_correct (width : Nat) (resetValue : Value width) :
    (description width resetValue).ImplementsCycleContract
      (cycleContract width resetValue) (Naming.ports width) :=
  Internal.construction_correct width resetValue

/-- The generated hierarchy implements the enabled-reset-counter contract. -/
theorem implements_contract (width : Nat) (resetValue : Value width) :
    Contracts.Cycle.Implements
      (moduleStructure width resetValue)
      (cycleContract width resetValue)
      (certification width resetValue).stateCorresponds :=
  (certification width resetValue).implements

end Silean.Modules.EnabledResetCounter
