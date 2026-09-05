import Silean.Authoring.ModuleDesign
import Silean.Authoring.ModuleCycleContract
import Silean.Contracts.Cycle.CycleContract
import Silean.Modules.HalfAdder.HalfAdder
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.OrPrimitive

namespace Silean.Modules

open Silean
open Silean.Authoring

/-! A one-bit full adder. Its contract states the direct three-input Boolean
behavior; the hardware implementation below is the standard composition of
two half adders and one OR gate. -/

module_design FullAdder where
  ports {
    input left : .bit,
    input right : .bit,
    input carryIn : .bit,
    output sum : .bit,
    output carryOut : .bit }

  instances {
    -- Adds the two operand bits.
    operands := HalfAdder.design,
    -- Adds carry-in to the operands' partial sum.
    carry := HalfAdder.design,
    -- Combines the two mutually exclusive carry candidates.
    combineCarry := Primitives.orDesign }

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

namespace Silean.Modules.FullAdder

open Silean

/-! ## Behavioral contract -/

/-- Low bit of the sum of three input bits. -/
def sumValue (left right carryIn : Bool) : Bool :=
  Primitives.xorValue (Primitives.xorValue left right) carryIn

/-- High bit of the sum of three input bits. -/
def carryValue (left right carryIn : Bool) : Bool :=
  (left && right) || (left && carryIn) || (right && carryIn)

module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule sum where
    reads := [left, right, carryIn]
    writes := { sum := sumValue left right carryIn }
  output_rule carryOut where
    reads := [left, right, carryIn]
    writes := { carryOut := carryValue left right carryIn }
  state_rule where
    reads := []
    next := {}

end Silean.Modules.FullAdder
