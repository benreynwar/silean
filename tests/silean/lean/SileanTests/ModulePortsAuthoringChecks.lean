import Silean.Authoring.ModulePorts
import Silean.Authoring.SignalSchemaDeclaration

namespace SileanTests.ModulePortsAuthoring

open Silean Silean.Authoring

namespace Simple

module_ports ports where
  input left : .bit,
  input carryIn (name := "carry_in") : .bit,
  output sum : .bit

example : inputMap.signalType .left = .bit := rfl
example : outputMap.signalType .sum = .bit := rfl
example : Naming.ports.inputs.name .carryIn = "carry_in" := rfl

end Simple

namespace Generic

module_ports ports (signalType : SignalType)
    with (typeNaming : Naming.SignalTypeNaming signalType :=
      Naming.SignalTypeNaming.positional signalType) where
  input value (schema := typeNaming) : signalType,
  input enable : .bit,
  output value (name := "value_out") (schema := typeNaming) : signalType

example (signalType : SignalType) :
    (inputMap signalType).signalType .value = signalType := rfl

example (signalType : SignalType) (typeNaming : Naming.SignalTypeNaming signalType) :
    (Naming.portsWithNaming signalType typeNaming).inputTypes .value = typeNaming := rfl

example (signalType : SignalType) :
    (Naming.ports signalType).outputs.name .value = "value_out" := rfl

end Generic

namespace Schema

signal_schema Pair (width : Nat) where
  flag : SignalSchema.bit,
  payload : SignalSchema.vector width .bit

abbrev pair := Pair.schema 2

module_ports ports (signalType : SignalType)
    with (schema : SignalSchema signalType :=
      SignalSchema.positional signalType) where
  input value (schema := schema) : signalType,
  output copied (schema := schema) : signalType

example : (Naming.portsWithNaming _ pair).inputTypes .value =
    pair := rfl

abbrev payload := Pair.field 2 .payload

example : payload.signalType = .vector 2 .bit := rfl
example : Pair.signalType 2 =
    .tuple (.cons .bit (.cons (.vector 2 .bit) .nil)) := rfl
example : Pair.field 2 .payload = SignalSchema.vector 2 .bit := rfl

end Schema

namespace OutputOnly

module_ports ports where
  output value : .bit

example : Input = NoSignal := rfl
example : ports.inputs = emptySignalMap := rfl
example : Naming.ports.outputs.name .value = "value" := rfl

end OutputOnly

namespace MultipleNamings

module_ports ports (leftType : SignalType) (rightType : SignalType)
    with
      (leftNaming : Naming.SignalTypeNaming leftType := .positional leftType),
      (rightNaming : Naming.SignalTypeNaming rightType := .positional rightType) where
  input left (schema := leftNaming) : leftType,
  input right (schema := rightNaming) : rightType,
  output valid : .bit

example (leftType rightType : SignalType)
    (leftNaming : Naming.SignalTypeNaming leftType)
    (rightNaming : Naming.SignalTypeNaming rightType) :
    (Naming.portsWithNaming leftType rightType leftNaming rightNaming).inputTypes .right =
      rightNaming := rfl

end MultipleNamings

end SileanTests.ModulePortsAuthoring
