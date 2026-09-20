import Silean.Authoring.CircuitDescriptionContracts
import Silean.Authoring.CircuitSelection
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Modules.ResetRegister.ResetRegisterDerived

/-! # Enabled reset register

An enabled reset register resets to a fixed value, loads `value` when enabled,
and otherwise retains its stored value. The readable construction shows the
feedback directly; expanded structure and certification live under
`Internal/`.
-/

namespace Silean.Modules.EnabledResetRegister

open Silean
open Silean.Authoring
open Authoring.CircuitDescription

module_ports ports (signalType : SignalType)
    with (typeNaming : Silean.Naming.SignalTypeNaming signalType :=
      .positional signalType) where
  input value (schema := typeNaming) : signalType,
  input enable : .bit,
  input reset : .bit,
  output value (name := "value_out") (schema := typeNaming) : signalType

open ports

noncomputable def construction (signalType : SignalType)
    (resetValue : signalType.Denote) :
    ModuleBuilder (ports signalType) Unit := do
  let value ← input signalType .value
  let enable ← input signalType .enable
  let reset ← input signalType .reset
  wire stored : signalType
  let current ← ResetRegister.place resetValue
    (← mux enable stored value) reset
  assign stored current
  output signalType .value current

noncomputable def description (signalType : SignalType)
    (resetValue : signalType.Denote) : Description :=
  ModuleBuilder.build (Naming.ports signalType)
    (construction signalType resetValue)

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

section AllowedStep

variable {signalType : SignalType}
  {resetValue : signalType.Denote}
  {step : (cycleContract signalType resetValue).Step}
  (allowed : (cycleContract signalType resetValue).Allows step)

include allowed

/-- An allowed step exposes the value stored before the clock edge. -/
theorem value_of_allowed :
    step.outputs .value = step.currentState .stored :=
  (observeRule_holds_iff signalType resetValue
    step.inputs step.currentState step.outputs).mp (allowed.1 .observe)

/-- Synchronous reset has priority over loading a new value. -/
theorem next_stored_of_allowed :
    step.nextState .stored =
      bif step.inputs .reset then resetValue
      else bif step.inputs .enable then step.inputs .value
      else step.currentState .stored := by
  rw [allowed.2]
  rfl

theorem next_stored_of_reset (reset : step.inputs .reset = true) :
    step.nextState .stored = resetValue := by
  rw [next_stored_of_allowed allowed, reset]
  rfl

theorem next_stored_of_enabled
    (notReset : step.inputs .reset = false)
    (enabled : step.inputs .enable = true) :
    step.nextState .stored = step.inputs .value := by
  rw [next_stored_of_allowed allowed, notReset, enabled]
  rfl

theorem next_stored_of_disabled
    (notReset : step.inputs .reset = false)
    (disabled : step.inputs .enable = false) :
    step.nextState .stored = step.currentState .stored := by
  rw [next_stored_of_allowed allowed, notReset, disabled]
  rfl

end AllowedStep

end Silean.Modules.EnabledResetRegister
