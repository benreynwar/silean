import Silean.FIRRTL
import Silean.Modules.AddSub.AddSubDerived

namespace SileanTests.AddSub

open Silean Silean.FIRRTL

def bits0 : Fin 0 → Bool := fun index => Fin.elim0 index
def bits4Three : Fin 4 → Bool := fun | 0 | 1 => true | 2 | 3 => false
def bits4Five : Fin 4 → Bool := fun | 0 | 2 => true | 1 | 3 => false
def bits4Thirteen : Fin 4 → Bool := fun | 0 | 2 | 3 => true | 1 => false
def bits4Fifteen : Fin 4 → Bool := fun _ => true

def inputs (width : Nat) (left right : Fin width → Bool) (subtract : Bool) :
    (Modules.AddSub.ports width).inputs.Values
  | .left => left
  | .right => right
  | .subtract => subtract

def outputs (width : Nat) (left right : Fin width → Bool) (subtract : Bool) :=
  ((Modules.AddSub.cycleContract width).evaluate
    (inputs width left right subtract) SignalMap.emptyValues).1

noncomputable example : Contracts.Cycle.ModuleCycleCertified
    (Modules.AddSub.ports 4) :=
  Modules.AddSub.certified 4

example : Contracts.Cycle.Implements
    (Modules.AddSub.moduleStructure 4) (Modules.AddSub.cycleContract 4)
    (Modules.AddSub.certification 4).stateCorresponds :=
  Modules.AddSub.implements_contract 4

-- Width zero has no result bits; addition has no carry and subtraction has no borrow.
#guard !(outputs 0 bits0 bits0 false .carryOut)
#guard outputs 0 bits0 bits0 true .carryOut

-- 3 + 5 = 8, while 3 - 5 wraps to 14 and borrows.
#guard BitVector.toNat 4 (outputs 4 bits4Three bits4Five false .result) == 8
#guard !(outputs 4 bits4Three bits4Five false .carryOut)
#guard BitVector.toNat 4 (outputs 4 bits4Three bits4Five true .result) == 14
#guard !(outputs 4 bits4Three bits4Five true .carryOut)

-- 13 - 5 = 8 without a borrow; 15 + 5 wraps and carries.
#guard BitVector.toNat 4 (outputs 4 bits4Thirteen bits4Five true .result) == 8
#guard outputs 4 bits4Thirteen bits4Five true .carryOut
#guard BitVector.toNat 4 (outputs 4 bits4Fifteen bits4Five false .result) == 4
#guard outputs 4 bits4Fifteen bits4Five false .carryOut

example (width : Nat) (left right : Fin width → Bool) (subtract : Bool) :
    BitVector.toNat width (outputs width left right subtract .result) =
      bif subtract then
        (BitVector.toNat width left + BitVector.cardinality width -
          BitVector.toNat width right) % BitVector.cardinality width
      else
        (BitVector.toNat width left + BitVector.toNat width right) %
          BitVector.cardinality width := by
  simpa [outputs, inputs, Contracts.Cycle.ModuleCycleContract.evaluateStep] using
    Modules.AddSub.result_toNat_of_allowed width
      ((Modules.AddSub.cycleContract width).evaluateStep_allowed
        (inputs width left right subtract) SignalMap.emptyValues)

example (width : Nat) (left right : Fin width → Bool) :
    outputs width left right true .carryOut =
      decide (BitVector.toNat width right ≤ BitVector.toNat width left) := by
  change @Eq Bool
    (((Modules.AddSub.cycleContract width).evaluate
      (inputs width left right true) SignalMap.emptyValues).1 .carryOut) _
  have equation := Modules.AddSub.cycleContract.carryOut width
    ((Modules.AddSub.cycleContract width).evaluateStep_allowed
      (inputs width left right true) SignalMap.emptyValues)
  change @Eq Bool
    (((Modules.AddSub.cycleContract width).evaluate
      (inputs width left right true) SignalMap.emptyValues).1 .carryOut)
    (Modules.AddSub.addSubBits width left right true).2 at equation
  exact equation.trans
    (Modules.AddSub.addSubBits_carry_subtract width left right)

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

#guard match renderRootModule (Modules.AddSub.naming 4) with
  | .error _ => false
  | .ok text =>
      ["public module AddSub_4", "input left : UInt<1>[4]",
       "input right : UInt<1>[4]", "input subtract : UInt<1>",
       "output result : UInt<1>[4]", "output carryOut : UInt<1>",
       "inst combiner_0", "inst bitwise_xor_0",
       "inst add_0 of add_ripple_4",
       "connect bitwise_xor_0.right, combiner_0.aggregate_0",
       "connect add_0.right, transformedRight",
       "connect add_0.carry_in, subtract"].all (contains text)

end SileanTests.AddSub
