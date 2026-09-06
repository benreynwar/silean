import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModuleDesign
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.Mux
import Silean.Modules.Register.Register

namespace Silean.Modules

open Silean
open Silean.Authoring

/-! A register which stores `value`, except that reset selects a fixed value. -/

namespace ResetRegister

module_ports ports (signalType : SignalType)
    with (typeNaming : Silean.Naming.SignalTypeNaming signalType :=
      .positional signalType) where
  input value (schema := typeNaming) : signalType,
  input reset : .bit,
  output value (name := "value_out") (schema := typeNaming) : signalType

end ResetRegister

module_design ResetRegister (signalType : SignalType)
    (resetValue : signalType.Denote)
    (specialization := .signalType signalType ::
      Modules.Constant.Naming.parameters signalType resetValue) where
  boundary (ResetRegister.ports signalType)
    (naming := ResetRegister.Naming.ports signalType)
  instances {
    -- Produces the value loaded during reset.
    resetValue := Modules.Constant.design signalType resetValue,
    -- Chooses between the ordinary input and reset value.
    selection := Modules.Mux.design signalType,
    -- Holds the selected value across cycles.
    storage := Modules.Register.design signalType }
  wiring {
    outputs {
      .value := storage.output }
    instance (.resetValue) {}
    instance (.selection) {
      .select := input.reset,
      .whenFalse := input.value,
      .whenTrue := resetValue.output }
    instance (.storage) {
      .input := selection.result }
  }

end Silean.Modules

namespace Silean.Modules.ResetRegister

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
    reads := [reset, value]
    next := { stored := bif reset then resetValue else value }

@[simp] theorem stateRule_apply_stored (signalType : SignalType)
    (resetValue : signalType.Denote)
    (inputs : (ports signalType).inputs.Values)
    (state : (Register.stateMap signalType).Values) :
    (stateRule signalType resetValue).apply inputs state .stored =
      bif inputs .reset then resetValue else inputs .value := by
  rfl

theorem next_stored_of_reset (signalType : SignalType)
    (resetValue : signalType.Denote)
    (inputs : (ports signalType).inputs.Values)
    (state : (Register.stateMap signalType).Values)
    (reset : inputs .reset = true) :
    (stateRule signalType resetValue).apply inputs state .stored = resetValue := by
  rw [stateRule_apply_stored, reset]
  rfl

theorem next_stored_of_not_reset (signalType : SignalType)
    (resetValue : signalType.Denote)
    (inputs : (ports signalType).inputs.Values)
    (state : (Register.stateMap signalType).Values)
    (notReset : inputs .reset = false) :
    (stateRule signalType resetValue).apply inputs state .stored = inputs .value := by
  rw [stateRule_apply_stored, notReset]
  rfl

end Silean.Modules.ResetRegister
