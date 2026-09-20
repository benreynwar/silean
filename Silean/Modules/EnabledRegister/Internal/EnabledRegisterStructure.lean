import Silean.Authoring.ModuleDesign
import Silean.Modules.EnabledRegister.EnabledRegister
import Silean.Modules.Mux.Mux
import Silean.Modules.Register.RegisterDerived

namespace Silean.Modules

open Silean
open Silean.Authoring

module_design EnabledRegister (signalType : SignalType)
    with (typeNaming : Silean.Naming.SignalTypeNaming signalType :=
      .positional signalType) where
  boundary (EnabledRegister.ports signalType)
    (naming := EnabledRegister.Naming.ports signalType)
    (namingWith := EnabledRegister.Naming.portsWithNaming signalType typeNaming)
  instances {
    selection (name := .indexed "mux" 0) := Modules.Mux.design signalType,
    storage (name := .indexed "register" 0) :=
      Modules.Register.design signalType }
  named_wires {
    stored := storage.output }
  wiring {
    outputs {
      .q := storage.output }
    instance (.selection) {
      .select := input.enable,
      .whenFalse := storage.output,
      .whenTrue := input.data }
    instance (.storage) {
      .input := selection.result }
  }

end Silean.Modules

namespace Silean.Modules.EnabledRegister.Internal

open Silean

@[simp] theorem selection_instance_name (signalType : SignalType) :
    EnabledRegister.Naming.instanceNames signalType .selection =
      .indexed "mux" 0 := rfl

@[simp] theorem storage_instance_name (signalType : SignalType) :
    EnabledRegister.Naming.instanceNames signalType .storage =
      .indexed "register" 0 := rfl

@[simp] theorem selection_child_ports (signalType : SignalType) :
    ((EnabledRegister.body signalType).instancePorts.ports .selection) =
      Mux.ports signalType := rfl

@[simp] theorem storage_child_ports (signalType : SignalType) :
    ((EnabledRegister.body signalType).instancePorts.ports .storage) =
      Register.ports signalType := rfl

end Silean.Modules.EnabledRegister.Internal
