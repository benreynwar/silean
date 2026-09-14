import Silean.Authoring.ModuleDesign
import Silean.Modules.BitwiseOr.BitwiseOr
import Silean.Modules.Mask.Mask
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.NotPrimitive

namespace Silean.Modules

open Silean
open Silean.Authoring

/-! A generic combinational mux built from masking and bitwise OR. -/

module_design Mux (signalType : SignalType)
    with (typeNaming : Silean.Naming.SignalTypeNaming signalType :=
      .positional signalType) where
  ports {
    input select : .bit,
    input whenFalse (schema := typeNaming) : signalType,
    input whenTrue (schema := typeNaming) : signalType,
    output result (schema := typeNaming) : signalType }
  instances {
    -- Produces the complement of the select bit.
    invertSelect := Primitives.notDesign,
    -- Passes the false branch only when select is low.
    chooseFalse := Mask.design signalType,
    -- Passes the true branch only when select is high.
    chooseTrue := Mask.design signalType,
    -- Combines the two mutually exclusive masked values.
    combine := BitwiseOr.design signalType }
  wiring {
    outputs {
      .result := combine.result }
    instance (.invertSelect) {
      .input := input.select }
    instance (.chooseFalse) {
      .value := input.whenFalse,
      .mask := invertSelect.output }
    instance (.chooseTrue) {
      .value := input.whenTrue,
      .mask := input.select }
    instance (.combine) {
      .left := chooseFalse.result,
      .right := chooseTrue.result }
  }

end Silean.Modules
