import Silean.Authoring.ModuleDesign
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.AndPrimitive
import Silean.Primitives.XorPrimitive

namespace Silean.Modules

open Silean
open Silean.Authoring

/-! A one-bit half adder. `sum` is XOR and `carry` is AND. -/

module_design HalfAdder where
  ports {
    input left : .bit,
    input right : .bit,
    output sum : .bit,
    output carry : .bit }

  instances {
    -- XOR produces the sum bit.
    sumGate (name := .indexed "xor" 0) := Primitives.xorDesign,
    -- AND produces the carry bit.
    carryGate (name := .indexed "and" 0) := Primitives.andDesign }

  wiring {
    outputs {
      .sum := sumGate.output,
      .carry := carryGate.output }
    instance (.sumGate) {
      .left := input.left,
      .right := input.right }
    instance (.carryGate) {
      .left := input.left,
      .right := input.right }
  }

end Silean.Modules
