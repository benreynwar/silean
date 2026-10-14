import Silean.Authoring.ModuleDesign
import Silean.Modules.HalfAdder.HalfAdder
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.AndPrimitive
import Silean.Primitives.XorPrimitive

namespace Silean.Modules

open Silean
open Silean.Authoring

/-! A one-bit half adder. `sum` is XOR and `carry` is AND. -/

module_design HalfAdder where
  boundary (HalfAdder.ports) (naming := HalfAdder.Naming.ports)

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
