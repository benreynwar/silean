import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModuleDesign
import Silean.Modules.Mux.Mux
import Silean.Modules.ResetRegister.ResetRegister

namespace Silean.Modules

open Silean
open Silean.Authoring

/-! A register which resets to a fixed value, loads a new value when enabled,
and otherwise retains its current value. -/

namespace EnabledResetRegister

module_ports ports (signalType : SignalType)
    with (typeNaming : Silean.Naming.SignalTypeNaming signalType :=
      .positional signalType) where
  input value (schema := typeNaming) : signalType,
  input enable : .bit,
  input reset : .bit,
  output value (name := "value_out") (schema := typeNaming) : signalType

end EnabledResetRegister

module_design EnabledResetRegister (signalType : SignalType)
    (resetValue : signalType.Denote)
    (specialization := .signalType signalType ::
      Modules.Constant.Naming.parameters signalType resetValue) where
  boundary (EnabledResetRegister.ports signalType)
    (naming := EnabledResetRegister.Naming.ports signalType)
  instances {
    -- Chooses between the new input and the stored value.
    selection := Modules.Mux.design signalType,
    -- Applies reset and stores the selected value.
    storage := Modules.ResetRegister.design signalType resetValue }
  wiring {
    outputs {
      .value := storage.value }
    instance (.selection) {
      .select := input.enable,
      .whenFalse := storage.value,
      .whenTrue := input.value }
    instance (.storage) {
      .value := selection.result,
      .reset := input.reset }
  }

end Silean.Modules

namespace Silean.Modules.EnabledResetRegister

open Silean
open Silean.Authoring

def namingWith {signalType : SignalType} (resetValue : signalType.Denote)
    (typeNaming : Silean.Naming.SignalTypeNaming signalType) :
    Silean.Naming.ModuleNaming (moduleStructure signalType resetValue) :=
  (naming signalType resetValue).withPorts
    (Naming.portsWithNaming signalType typeNaming)

@[reducible] def designWith {signalType : SignalType}
    (resetValue : signalType.Denote)
    (typeNaming : Silean.Naming.SignalTypeNaming signalType) :
    Silean.Naming.NamedModule :=
  ⟨ports signalType, moduleStructure signalType resetValue,
    namingWith resetValue typeNaming⟩

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

@[simp] theorem stateRule_apply_stored (signalType : SignalType)
    (resetValue : signalType.Denote)
    (inputs : (ports signalType).inputs.Values)
    (state : (Register.stateMap signalType).Values) :
    (stateRule signalType resetValue).apply inputs state .stored =
      bif inputs .reset then resetValue
      else bif inputs .enable then inputs .value else state .stored := by
  rfl

theorem next_stored_of_reset (signalType : SignalType)
    (resetValue : signalType.Denote)
    (inputs : (ports signalType).inputs.Values)
    (state : (Register.stateMap signalType).Values)
    (reset : inputs .reset = true) :
    (stateRule signalType resetValue).apply inputs state .stored = resetValue := by
  rw [stateRule_apply_stored, reset]
  rfl

theorem next_stored_of_enabled (signalType : SignalType)
    (resetValue : signalType.Denote)
    (inputs : (ports signalType).inputs.Values)
    (state : (Register.stateMap signalType).Values)
    (notReset : inputs .reset = false) (enabled : inputs .enable = true) :
    (stateRule signalType resetValue).apply inputs state .stored = inputs .value := by
  rw [stateRule_apply_stored, notReset, enabled]
  rfl

theorem next_stored_of_disabled (signalType : SignalType)
    (resetValue : signalType.Denote)
    (inputs : (ports signalType).inputs.Values)
    (state : (Register.stateMap signalType).Values)
    (notReset : inputs .reset = false) (disabled : inputs .enable = false) :
    (stateRule signalType resetValue).apply inputs state .stored = state .stored := by
  rw [stateRule_apply_stored, notReset, disabled]
  rfl

end Silean.Modules.EnabledResetRegister
