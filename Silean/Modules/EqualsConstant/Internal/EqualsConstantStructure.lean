import Silean.Authoring.ModuleDesign
import Silean.Modules.Constant.Constant
import Silean.Modules.Equality.Equality

namespace Silean.Modules

open Silean
open Silean.Authoring

/-! Expanded typed structure for comparison against a fixed value. -/

namespace EqualsConstant

module_ports ports (signalType : SignalType)
    with (typeNaming : Silean.Naming.SignalTypeNaming signalType :=
      .positional signalType) where
  input value (schema := typeNaming) : signalType,
  output result : .bit

end EqualsConstant

module_design EqualsConstant (signalType : SignalType)
    (constant : signalType.Denote)
    (specialization := .signalType signalType ::
      Constant.Naming.parameters signalType constant) where
  boundary (EqualsConstant.ports signalType)
    (naming := EqualsConstant.Naming.ports signalType)
  instances {
    constantValue (name := .indexed "constant" 0) :=
      Constant.design signalType constant,
    equality (name := .indexed "equality" 0) := Equality.design signalType }
  wiring {
    outputs {
      .result := equality.result }
    instance (.constantValue) {}
    instance (.equality) {
      .left := input.value,
      .right := constantValue.output }
  }

end Silean.Modules
