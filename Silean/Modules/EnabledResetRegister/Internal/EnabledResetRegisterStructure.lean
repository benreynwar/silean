import Silean.Authoring.ModuleDesign
import Silean.Modules.Mux.Mux
import Silean.Modules.ResetRegister.ResetRegister

namespace Silean.Modules

open Silean
open Silean.Authoring

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
      Modules.Constant.Naming.parameters signalType resetValue)
    with (typeNaming : Silean.Naming.SignalTypeNaming signalType :=
      .positional signalType) where
  boundary (EnabledResetRegister.ports signalType)
    (naming := EnabledResetRegister.Naming.ports signalType)
    (namingWith := EnabledResetRegister.Naming.portsWithNaming
      signalType typeNaming)
  instances {
    selection (name := .indexed "mux" 0) := Modules.Mux.design signalType,
    storage (name := .indexed "reset_register" 0) :=
      Modules.ResetRegister.design signalType resetValue }
  named_wires {
    stored := storage.value }
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
