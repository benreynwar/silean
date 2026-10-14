import Silean.Authoring.ModuleDesign
import Silean.Modules.BitwiseOr.BitwiseOr
import Silean.Modules.Mask.Mask
import Silean.Modules.Mux.Mux
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.NotPrimitive

namespace Silean.Modules

open Silean
open Silean.Authoring

/-! A generic combinational mux built from masking and bitwise OR. -/

module_design Mux (signalType : SignalType)
    with (typeNaming : Silean.Naming.SignalTypeNaming signalType :=
      .positional signalType) where
  boundary (Mux.ports signalType)
    (naming := Mux.Naming.ports signalType)
    (namingWith := Mux.Naming.portsWithNaming signalType typeNaming)
  instances {
    -- Produces the complement of the select bit.
    invertSelect (name := .indexed "not" 0) := Primitives.notDesign,
    -- Passes the false branch only when select is low.
    chooseFalse (name := .indexed "mask" 0) := Mask.design signalType,
    -- Passes the true branch only when select is high.
    chooseTrue (name := .indexed "mask" 1) := Mask.design signalType,
    -- Combines the two mutually exclusive masked values.
    combine (name := .indexed "bitwise_or" 0) := BitwiseOr.design signalType }
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
