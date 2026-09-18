import Silean.Authoring.ModuleDesign
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.Mux
import Silean.Modules.Register.Register

namespace Silean.Modules

open Silean
open Silean.Authoring

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
      Modules.Constant.Naming.parameters signalType resetValue)
    with (typeNaming : Silean.Naming.SignalTypeNaming signalType :=
      .positional signalType) where
  boundary (ResetRegister.ports signalType)
    (naming := ResetRegister.Naming.ports signalType)
    (namingWith := ResetRegister.Naming.portsWithNaming signalType typeNaming)
  instances {
    resetValue := Modules.Constant.design signalType resetValue,
    selection := Modules.Mux.design signalType,
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

namespace Silean.Modules.ResetRegister.Internal

open Silean

@[simp] theorem resetValue_instance_name (signalType : SignalType)
    (resetValue : signalType.Denote) :
    ResetRegister.Naming.instanceNames signalType resetValue .resetValue =
      "resetValue" := rfl

@[simp] theorem selection_instance_name (signalType : SignalType)
    (resetValue : signalType.Denote) :
    ResetRegister.Naming.instanceNames signalType resetValue .selection =
      "selection" := rfl

@[simp] theorem storage_instance_name (signalType : SignalType)
    (resetValue : signalType.Denote) :
    ResetRegister.Naming.instanceNames signalType resetValue .storage =
      "storage" := rfl

@[simp] theorem resetValue_child_ports (signalType : SignalType)
    (resetValue : signalType.Denote) :
    ((ResetRegister.body signalType resetValue).instancePorts.ports
      .resetValue) = Constant.ports signalType := rfl

@[simp] theorem selection_child_ports (signalType : SignalType)
    (resetValue : signalType.Denote) :
    ((ResetRegister.body signalType resetValue).instancePorts.ports
      .selection) = Mux.ports signalType := rfl

@[simp] theorem storage_child_ports (signalType : SignalType)
    (resetValue : signalType.Denote) :
    ((ResetRegister.body signalType resetValue).instancePorts.ports
      .storage) = Register.ports signalType := rfl

end Silean.Modules.ResetRegister.Internal
