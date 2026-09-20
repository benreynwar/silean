import Silean.Authoring.CircuitDescriptionContracts
import Silean.Authoring.CircuitSelection
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Modules.Register.RegisterDerived

/-! # Enabled register

An enabled register loads `data` when `enable` is high and otherwise feeds its
stored value back to itself. The construction shows that feedback directly;
expanded structure and certification live under `Internal/`.
-/

namespace Silean.Modules.EnabledRegister

open Silean
open Silean.Authoring
open Authoring.CircuitDescription

module_ports ports (signalType : SignalType)
    with (typeNaming : Silean.Naming.SignalTypeNaming signalType :=
      .positional signalType) where
  input data (schema := typeNaming) : signalType,
  input enable : .bit,
  output q (schema := typeNaming) : signalType

open ports

noncomputable def construction (signalType : SignalType) :
    ModuleBuilder (ports signalType) Unit := do
  let data ← input signalType .data
  let enable ← input signalType .enable
  wire stored : signalType
  let current ← Register.place (← mux enable stored data)
  assign stored current
  output signalType .q current

noncomputable def description (signalType : SignalType) : Description :=
  ModuleBuilder.build (Naming.ports signalType) (construction signalType)

module_cycle_contract cycleContract (signalType : SignalType)
    for ports signalType where
  state := Register.stateMap signalType
  output_rule observe where
    reads := []
    writes := { q := state .stored }
  state_rule where
    reads := [enable, data]
    next := { stored := bif enable then data else state .stored }

section AllowedStep

variable {signalType : SignalType}
  {step : (cycleContract signalType).Step}
  (allowed : (cycleContract signalType).Allows step)

include allowed

/-- An allowed step exposes the value stored before the clock edge. -/
theorem q_of_allowed : step.outputs .q = step.currentState .stored :=
  (observeRule_holds_iff signalType
    step.inputs step.currentState step.outputs).mp (allowed.1 .observe)

/-- Enable chooses between loading new data and retaining the stored value. -/
theorem next_stored_of_allowed :
    step.nextState .stored =
      bif step.inputs .enable then step.inputs .data
      else step.currentState .stored := by
  rw [allowed.2]
  rfl

theorem next_stored_of_enabled (enabled : step.inputs .enable = true) :
    step.nextState .stored = step.inputs .data := by
  rw [next_stored_of_allowed allowed, enabled]
  rfl

theorem next_stored_of_disabled (disabled : step.inputs .enable = false) :
    step.nextState .stored = step.currentState .stored := by
  rw [next_stored_of_allowed allowed, disabled]
  rfl

end AllowedStep

end Silean.Modules.EnabledRegister
