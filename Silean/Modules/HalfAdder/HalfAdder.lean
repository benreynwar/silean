import Silean.Authoring.CircuitLogic
import Silean.Authoring.CircuitDescriptionContracts
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts

/-! # Half adder

The authored circuit makes the hardware definition explicit: XOR produces the
sum bit and AND produces the carry bit. The exact cycle contract below gives
the same behavior without referring to that implementation.

The generated typed structure and its proof are deliberately downstream of
this file. Their public, derived interface is `HalfAdderDerived.lean`.
-/

namespace Silean.Modules.HalfAdder

open Silean
open Silean.Authoring
open Authoring.CircuitDescription
open scoped Authoring

module_ports ports where
  input left : .bit,
  input right : .bit,
  output sum : .bit,
  output carry : .bit

open ports

noncomputable def construction : ModuleBuilder ports Unit := do
  let left ← input .left
  let right ← input .right
  output .sum (← left ^^^ right)
  output .carry (← left &&& right)

noncomputable def description : Description :=
  ModuleBuilder.build Naming.ports construction

/-! ## Exact cycle behavior -/

def sumValue (left right : Bool) : Bool := Primitives.xorValue left right
def carryValue (left right : Bool) : Bool := left && right

module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule sum where
    reads := [left, right]
    writes := { sum := sumValue left right }
  output_rule carry where
    reads := [left, right]
    writes := { carry := carryValue left right }
  state_rule where
    reads := []
    next := {}

/-- A half adder's two output bits encode the natural-number sum of its inputs. -/
theorem numeric_value_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    (step.outputs .sum).toNat + 2 * (step.outputs .carry).toNat =
      (step.inputs .left).toNat + (step.inputs .right).toNat := by
  rw [cycleContract.sum allowed, cycleContract.carry allowed]
  exact Primitives.xor_toNat_add_twice_and _ _

end Silean.Modules.HalfAdder
