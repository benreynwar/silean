import Silean.Authoring.CircuitDescription
import Silean.Authoring.ModuleCycleContract
import Silean.Modules.EnabledRegister.Internal.EnabledRegisterStructure

/-! # Enabled register

An enabled register loads `data` on a clock edge when `enable` is high and
otherwise feeds its stored value back to itself. The description below shows
that feedback directly; the expanded typed hierarchy lives under `Internal/`.
-/

namespace Silean.Modules.EnabledRegister.Description

open Silean
open Silean.Authoring.CircuitDescription

/-- A mux selects either the feedback value or new data, and a register stores
the result. -/
noncomputable def construction (signalType : SignalType) : Builder Unit := do
  let data <- input "data" signalType
  let enable <- input "enable" .bit
  let stored <- wire "stored" signalType
  let selected <- Modules.Mux.placeNamed "selection" enable stored data
  let current <- Modules.Register.placeNamed "storage" selected
  assign stored current
  output "q" current

noncomputable def description (signalType : SignalType) : Description :=
  build (construction signalType)

end Silean.Modules.EnabledRegister.Description

namespace Silean.Modules.EnabledRegister
open Silean
open Silean.Authoring

open Authoring.CircuitDescription

/-! ## Placement -/

/-- Place an enabled register under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Silean.Naming.SourceName)
    (data : Net signalType) (enable : Net .bit) : Builder (Net signalType) := do
  let child <- Authoring.CircuitDescription.placeNamed name (design signalType) fun
    | .data => data
    | .enable => enable
  pure (child .q)

/-- Place an enabled register using the next conventional indexed name. -/
noncomputable def place (data : Net signalType)
    (enable : Net .bit) : Builder (Net signalType) := do
  let child <- placeIndexed "enabled_register" (design signalType) fun
    | .data => data
    | .enable => enable
  pure (child .q)

/-! ## Exact cycle behavior -/

module_cycle_contract cycleContract (signalType : SignalType)
    for ports signalType where
  state := Modules.Register.stateMap signalType
  output_rule observe where
    reads := []
    writes := { q := state .stored }
  state_rule where
    reads := [enable, data]
    next := { stored := bif enable then data else state .stored }
end Silean.Modules.EnabledRegister
