import Silean.Authoring.CircuitDescription
import Silean.Authoring.ModuleCycleContract
import Silean.Modules.FullAdder.Internal.FullAdderStructure
import Silean.Modules.HalfAdder.HalfAdder
import Silean.Primitives.Or

/-! # Full adder

The authored circuit is the standard hierarchy of two half adders and one OR
gate. Its exact cycle contract states the direct three-input Boolean behavior,
independently of that implementation.

The expanded typed structure and its verification are supporting machinery in
`Internal/`; the main reader-facing results are in `FullAdderTheorems.lean`.
-/

namespace Silean.Modules.FullAdder

open Silean
open Silean.Authoring
open Authoring.CircuitDescription

namespace Description

noncomputable def construction : Builder Unit := do
  let left ← input "left" .bit
  let right ← input "right" .bit
  let carryIn ← input "carryIn" .bit
  let operands ← HalfAdder.place left right
  let carry ← HalfAdder.place operands.sum carryIn
  output "sum" carry.sum
  output "carryOut" (← Primitives.Or.place operands.carry carry.carry)

noncomputable def description : Description := build construction

end Description

/-! ## Exact cycle behavior -/

/-- Low bit of the sum of three input bits. -/
def sumValue (left right carryIn : Bool) : Bool :=
  Primitives.xorValue (Primitives.xorValue left right) carryIn

/-- High bit of the sum of three input bits. -/
def carryValue (left right carryIn : Bool) : Bool :=
  (left && right) || (left && carryIn) || (right && carryIn)

/-- The observable relationship between a full adder's inputs and outputs. -/
structure Behavior (inputs : ports.inputs.Values)
    (outputs : ports.outputs.Values) : Prop where
  sum : outputs .sum = sumValue (inputs .left) (inputs .right) (inputs .carryIn)
  carryOut : outputs .carryOut =
    carryValue (inputs .left) (inputs .right) (inputs .carryIn)

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

namespace Behavior

/-- Turn an allowed contract step into the full adder's simpler observable
`Behavior`. -/
theorem of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    Behavior step.inputs step.outputs :=
  ⟨(sumRule_holds_iff step.inputs step.currentState step.outputs).mp
      (allowed.1 .sum),
    (carryOutRule_holds_iff step.inputs step.currentState step.outputs).mp
      (allowed.1 .carryOut)⟩

end Behavior

end Silean.Modules.FullAdder
