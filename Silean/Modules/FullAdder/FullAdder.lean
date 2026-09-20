import Silean.Authoring.CircuitDescriptionContracts
import Silean.Authoring.CircuitLogic
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Modules.HalfAdder.HalfAdderDerived

/-! # Full adder

The construction is the standard hierarchy of two half adders and one OR gate.
The cycle contract states the same three-input Boolean behavior independently
of that implementation.
-/

namespace Silean.Modules.FullAdder

open Authoring Authoring.CircuitDescription
open scoped Authoring

module_ports ports where
  input left : .bit,
  input right : .bit,
  input carryIn : .bit,
  output sum : .bit,
  output carryOut : .bit

open ports

noncomputable def construction : ModuleBuilder ports Unit := do
  let left ← input .left
  let right ← input .right
  let carryIn ← input .carryIn
  let operands ← halfAdder left right
  let carry ← halfAdder operands.sum carryIn
  output .sum carry.sum
  output .carryOut (← operands.carry ||| carry.carry)

noncomputable def description : Description :=
  ModuleBuilder.build Naming.ports construction

def sumValue (left right carryIn : Bool) : Bool :=
  Primitives.xorValue (Primitives.xorValue left right) carryIn

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

/-- A full adder's outputs encode the natural-number sum of its inputs. -/
theorem numeric_value_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    (step.outputs .sum).toNat + 2 * (step.outputs .carryOut).toNat =
      (step.inputs .left).toNat + (step.inputs .right).toNat +
        (step.inputs .carryIn).toNat := by
  rw [cycleContract.sum allowed, cycleContract.carryOut allowed]
  change
    (sumValue (step.inputs .left) (step.inputs .right)
      (step.inputs .carryIn)).toNat +
        2 * (carryValue (step.inputs .left) (step.inputs .right)
          (step.inputs .carryIn)).toNat = _
  cases step.inputs .left <;> cases step.inputs .right <;>
    cases step.inputs .carryIn <;> decide

end Silean.Modules.FullAdder
