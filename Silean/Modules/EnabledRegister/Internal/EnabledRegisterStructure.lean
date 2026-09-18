import Silean.Authoring.ModuleDesign
import Silean.Modules.Mux.Mux
import Silean.Modules.Register.Register

namespace Silean.Modules

open Silean
open Silean.Authoring

module_design EnabledRegister (signalType : SignalType)
    with (typeNaming : Silean.Naming.SignalTypeNaming signalType :=
      .positional signalType) where
  ports {
    input data (schema := typeNaming) : signalType,
    input enable : .bit,
    output q (schema := typeNaming) : signalType }
  instances {
    selection := Modules.Mux.design signalType,
    storage := Modules.Register.design signalType }
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
    EnabledRegister.Naming.instanceNames signalType .selection = "selection" := rfl

@[simp] theorem storage_instance_name (signalType : SignalType) :
    EnabledRegister.Naming.instanceNames signalType .storage = "storage" := rfl

@[simp] theorem selection_child_ports (signalType : SignalType) :
    ((EnabledRegister.body signalType).instancePorts.ports .selection) =
      Mux.ports signalType := rfl

@[simp] theorem storage_child_ports (signalType : SignalType) :
    ((EnabledRegister.body signalType).instancePorts.ports .storage) =
      Register.ports signalType := rfl

end Silean.Modules.EnabledRegister.Internal
