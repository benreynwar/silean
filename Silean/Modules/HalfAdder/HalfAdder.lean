import Silean.Authoring.ModuleDesign
import Silean.Authoring.ModuleCycleContract
import Silean.Contracts.Cycle.CycleContract
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
    sumGate := Primitives.xorDesign,
    -- AND produces the carry bit.
    carryGate := Primitives.andDesign }

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

namespace Silean.Modules.HalfAdder

open Silean

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

theorem sum_of_evaluatesTo (inputs : ports.inputs.Values)
    (state : cycleContract.state.Values) (outputs : ports.outputs.Values)
    (nextState : cycleContract.state.Values)
    (evaluates : cycleContract.EvaluatesTo inputs state outputs nextState) :
    outputs .sum = sumValue (inputs .left) (inputs .right) :=
  (sumRule_holds_iff inputs state outputs).mp (evaluates.1 .sum)

theorem carry_of_evaluatesTo (inputs : ports.inputs.Values)
    (state : cycleContract.state.Values) (outputs : ports.outputs.Values)
    (nextState : cycleContract.state.Values)
    (evaluates : cycleContract.EvaluatesTo inputs state outputs nextState) :
    outputs .carry = carryValue (inputs .left) (inputs .right) :=
  (carryRule_holds_iff inputs state outputs).mp (evaluates.1 .carry)

theorem sum_eq_true_of_evaluatesTo (inputs : ports.inputs.Values)
    (state : cycleContract.state.Values) (outputs : ports.outputs.Values)
    (nextState : cycleContract.state.Values)
    (evaluates : cycleContract.EvaluatesTo inputs state outputs nextState) :
    outputs .sum = true ↔ inputs .left ≠ inputs .right := by
  rw [sum_of_evaluatesTo inputs state outputs nextState evaluates]
  exact Primitives.xor_eq_true_iff _ _

theorem carry_eq_true_of_evaluatesTo (inputs : ports.inputs.Values)
    (state : cycleContract.state.Values) (outputs : ports.outputs.Values)
    (nextState : cycleContract.state.Values)
    (evaluates : cycleContract.EvaluatesTo inputs state outputs nextState) :
    outputs .carry = true ↔ inputs .left = true ∧ inputs .right = true := by
  rw [carry_of_evaluatesTo inputs state outputs nextState evaluates]
  cases inputs .left <;> cases inputs .right <;> simp [carryValue]

theorem numeric_value_of_evaluatesTo (inputs : ports.inputs.Values)
    (state : cycleContract.state.Values) (outputs : ports.outputs.Values)
    (nextState : cycleContract.state.Values)
    (evaluates : cycleContract.EvaluatesTo inputs state outputs nextState) :
    (outputs .sum).toNat + 2 * (outputs .carry).toNat =
      (inputs .left).toNat + (inputs .right).toNat := by
  rw [sum_of_evaluatesTo inputs state outputs nextState evaluates,
    carry_of_evaluatesTo inputs state outputs nextState evaluates]
  exact Primitives.xor_toNat_add_twice_and _ _

end Silean.Modules.HalfAdder
