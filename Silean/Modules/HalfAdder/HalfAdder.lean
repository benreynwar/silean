import Silean.Authoring.CircuitLogic
import Silean.Authoring.ModuleCycleContract
import Silean.Modules.HalfAdder.Internal.HalfAdderStructure

/-! # Half adder

The authored circuit makes the hardware definition explicit: XOR produces the
sum bit and AND produces the carry bit. The exact cycle contract below gives
the same behavior without referring to that implementation.

The expanded typed structure and its verification are supporting machinery in
`Internal/`; the main reader-facing results are in `HalfAdderTheorems.lean`.
-/

namespace Silean.Modules.HalfAdder

open Silean
open Silean.Authoring
open Authoring.CircuitDescription
open scoped Authoring.CircuitLogic

namespace Description

noncomputable def construction : Builder Unit := do
  let left ← input "left" .bit
  let right ← input "right" .bit
  output "sum" (← left ^^^ right)
  output "carry" (← left &&& right)

noncomputable def description : Description := build construction

end Description

/-- The two nets produced when a half adder is placed as a child. -/
structure PlacedOutputs where
  sum : Net .bit
  carry : Net .bit

/-- Place a half adder in a circuit description. -/
noncomputable def place (left right : Net .bit) : Builder PlacedOutputs := do
  let child ← placeIndexed "half_adder" design fun
    | .left => left
    | .right => right
  pure { sum := child .sum, carry := child .carry }

/-! ## Exact cycle behavior -/

def sumValue (left right : Bool) : Bool := Primitives.xorValue left right
def carryValue (left right : Bool) : Bool := left && right

/-- The observable relationship between a half adder's inputs and outputs. -/
structure Behavior (inputs : ports.inputs.Values)
    (outputs : ports.outputs.Values) : Prop where
  sum : outputs .sum = sumValue (inputs .left) (inputs .right)
  carry : outputs .carry = carryValue (inputs .left) (inputs .right)

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

namespace Behavior

/-- Turn an allowed contract step into the half adder's simpler observable
`Behavior`. -/
theorem of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    Behavior step.inputs step.outputs :=
  ⟨(sumRule_holds_iff step.inputs step.currentState step.outputs).mp
      (allowed.1 .sum),
    (carryRule_holds_iff step.inputs step.currentState step.outputs).mp
      (allowed.1 .carry)⟩

end Behavior

end Silean.Modules.HalfAdder
