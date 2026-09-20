import Silean.Authoring.ModuleDesign
import Silean.Modules.FullAdder.FullAdder
import Silean.Modules.HalfAdder.HalfAdderDerived
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.OrPrimitive

namespace Silean.Modules

open Silean
open Silean.Authoring

/-! A one-bit full adder. Its contract states the direct three-input Boolean
behavior; the hardware implementation below is the standard composition of
two half adders and one OR gate. -/

module_design FullAdder where
  boundary (FullAdder.ports) (naming := FullAdder.Naming.ports)

  instances {
    -- Adds the two operand bits.
    operands (name := .indexed "half_adder" 0) := HalfAdder.design,
    -- Adds carry-in to the operands' partial sum.
    carry (name := .indexed "half_adder" 1) := HalfAdder.design,
    -- Combines the two mutually exclusive carry candidates.
    combineCarry (name := .indexed "or" 0) := Primitives.orDesign }

  wiring {
    outputs {
      -- The second half adder produces the final sum.
      .sum := carry.sum,
      -- The OR gate combines carry from either addition stage.
      .carryOut := combineCarry.output }
    -- First add the two operand bits.
    instance (.operands) {
      .left := input.left,
      .right := input.right }
    -- Then add carry-in to their partial sum.
    instance (.carry) {
      .left := operands.sum,
      .right := input.carryIn }
    -- Either half-adder carry produces carry-out.
    instance (.combineCarry) {
      .left := operands.carry,
      .right := carry.carry }
  }

end Silean.Modules
