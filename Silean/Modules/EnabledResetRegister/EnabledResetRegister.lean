import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.CircuitSelection
import Silean.Modules.EnabledResetRegister.Internal.EnabledResetRegisterStructure
import Silean.Modules.Mux.Mux
import Silean.Modules.ResetRegister.ResetRegister

/-! A register which resets to a fixed value, loads a new value when enabled,
and otherwise retains its current value.

This file contains the authored circuit and its exact state-transition
contract. `EnabledResetRegisterTheorems.lean` states its useful consequences
and the structural guarantee; certification details remain under `Internal/`.
-/


namespace Silean.Modules.EnabledResetRegister.Description

open Silean
open Silean.Authoring.CircuitDescription
open Silean.Authoring.CircuitLogic

/-- A Verilog-style description of the feedback path. Finalization resolves
the forward-declared `stored` wire to the reset register's output while
retaining its name for emission and correspondence checking. -/
noncomputable def construction (signalType : SignalType)
    (resetValue : signalType.Denote) : Builder Unit := do
  let value <- input "value" signalType
  let enable <- input "enable" .bit
  let reset <- input "reset" .bit
  wire stored : signalType
  let current <- ResetRegister.place resetValue (← mux enable stored value) reset
  assign stored current
  output "value_out" current

noncomputable def description (signalType : SignalType)
    (resetValue : signalType.Denote) : Description :=
  build (construction signalType resetValue)

end Silean.Modules.EnabledResetRegister.Description

namespace Silean.Modules.EnabledResetRegister

open Silean
open Silean.Authoring
open Authoring.CircuitDescription

/-! ## Placement -/

/-- Place an enabled reset register under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Silean.Naming.SourceName)
    (resetValue : signalType.Denote) (value : Net signalType)
    (enable reset : Net .bit) : Builder (Net signalType) := do
  let child ← Authoring.CircuitDescription.placeNamed name
    (design signalType resetValue) fun
      | .value => value
      | .enable => enable
      | .reset => reset
  pure (child .value)

/-- Place an enabled reset register using the next conventional indexed name. -/
noncomputable def place (resetValue : signalType.Denote)
    (value : Net signalType) (enable reset : Net .bit) :
    Builder (Net signalType) := do
  let child ← placeIndexed "enabled_reset_register"
    (design signalType resetValue) fun
      | .value => value
      | .enable => enable
      | .reset => reset
  pure (child .value)

attribute [circuit_description] placeNamed place

/-! ## Exact cycle behavior -/

module_cycle_contract cycleContract (signalType : SignalType)
    (resetValue : signalType.Denote) for ports signalType where
  state := Modules.Register.stateMap signalType
  output_rule observe where
    reads := []
    writes := { value := state .stored }
  state_rule where
    reads := [reset, enable, value]
    next := { stored := bif reset then resetValue
      else bif enable then value else state .stored }

end Silean.Modules.EnabledResetRegister
