import Silean.FIRRTL
import Silean.Modules.Add.AddTheorems

namespace Silean.Examples.Checks.Add

open Silean Silean.FIRRTL

noncomputable example : Contracts.Cycle.ModuleCycleCertified (Modules.Add.ports 0) :=
  Modules.Add.certified 0
noncomputable example : Contracts.Cycle.ModuleCycleCertified (Modules.Add.ports 1) :=
  Modules.Add.certified 1
noncomputable example : Contracts.Cycle.ModuleCycleCertified (Modules.Add.ports 4) :=
  Modules.Add.certified 4

def bits0 : Fin 0 → Bool := fun index => Fin.elim0 index
def bits1Zero : Fin 1 → Bool := fun _ => false
def bits1One : Fin 1 → Bool := fun _ => true
def bits4Three : Fin 4 → Bool := fun | 0 | 1 => true | 2 | 3 => false
def bits4One : Fin 4 → Bool := fun | 0 => true | 1 | 2 | 3 => false
def bits4Five : Fin 4 → Bool := fun | 0 | 2 => true | 1 | 3 => false
def bits4Fifteen : Fin 4 → Bool := fun _ => true

def inputs (width : Nat) (left right : Fin width → Bool) (carryIn : Bool) :
    (Modules.Add.ports width).inputs.Values
  | .left => left
  | .right => right
  | .carryIn => carryIn

def outputs (width : Nat) (left right : Fin width → Bool) (carryIn : Bool) :=
  ((Modules.Add.cycleContract width).evaluate
    (inputs width left right carryIn) SignalMap.emptyValues).1

#guard !(outputs 0 bits0 bits0 false .carryOut)
#guard outputs 0 bits0 bits0 true .carryOut
#guard BitVector.toNat 1 (outputs 1 bits1Zero bits1Zero true .result) == 1
#guard BitVector.toNat 1 (outputs 1 bits1One bits1One false .result) == 0
#guard outputs 1 bits1One bits1One false .carryOut
#guard BitVector.toNat 4 (outputs 4 bits4Three bits4Five false .result) == 8
#guard !(outputs 4 bits4Three bits4Five false .carryOut)
#guard BitVector.toNat 4 (outputs 4 bits4Fifteen bits4One true .result) == 1
#guard outputs 4 bits4Fifteen bits4One true .carryOut

example (width : Nat) (left right : Fin width → Bool) (carryIn : Bool) :
    BitVector.toNat width (outputs width left right carryIn .result) +
        2 ^ width * (outputs width left right carryIn .carryOut).toNat =
      BitVector.toNat width left + BitVector.toNat width right + carryIn.toNat := by
  have behavior := Modules.Add.Behavior.of_allowed width
    ((Modules.Add.cycleContract width).evaluateStep_allowed
      (inputs width left right carryIn) SignalMap.emptyValues)
  simpa [outputs, inputs, Contracts.Cycle.ModuleCycleContract.evaluateStep] using
    behavior.numeric_value

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

#guard match renderRootModule (Modules.Add.Naming.naming 0) with
  | .error _ => false
  | .ok text =>
      ["public module add_base", "input left : UInt<1>[0]",
       "input right : UInt<1>[0]", "input carry_in : UInt<1>",
       "output result : UInt<1>[0]", "output carry_out : UInt<1>",
       "connect carry_out, carry_in"].all (contains text)

#guard match renderRootModule (Modules.Add.Naming.naming 3) with
  | .error _ => false
  | .ok text =>
      ["public module add_ripple_3", "inst left_split", "inst right_split",
       "inst add_lower of add_ripple_2",
       "inst add_high_bit of FullAdder",
       "connect add_high_bit.left, left_split.component_2",
       "connect add_high_bit.right, right_split.component_2",
       "connect add_high_bit.carryIn, add_lower.carry_out"].all (contains text)

end Silean.Examples.Checks.Add
