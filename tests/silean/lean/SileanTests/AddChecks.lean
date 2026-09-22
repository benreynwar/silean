import Silean.FIRRTL
import Silean.Modules.Add.AddDerived

namespace SileanTests.Add

open Silean Silean.FIRRTL

def bits (width : Nat) (value : Int) : Fin width → Bool :=
  BitVector.ofBitVec (BitVec.ofInt width value)

def inputs (leftWidth rightWidth : Nat)
    (leftSigned rightSigned extendOutput : Bool)
    (left : Fin leftWidth → Bool) (right : Fin rightWidth → Bool) :
    (Modules.Add.ports leftWidth rightWidth leftSigned rightSigned
      extendOutput).inputs.Values
  | .left => left
  | .right => right

def outputs (leftWidth rightWidth : Nat)
    (leftSigned rightSigned extendOutput : Bool)
    (left : Fin leftWidth → Bool) (right : Fin rightWidth → Bool) :=
  ((Modules.Add.cycleContract leftWidth rightWidth leftSigned rightSigned
    extendOutput).evaluate
      (inputs leftWidth rightWidth leftSigned rightSigned extendOutput left right)
      SignalMap.emptyValues).1

noncomputable example : Contracts.Cycle.ModuleCycleCertified
    (Modules.Add.ports 3 5 false true true) :=
  Modules.Add.certified 3 5 false true true

example : Contracts.Cycle.Implements
    (Modules.Add.moduleStructure 3 5 false true true)
    (Modules.Add.cycleContract 3 5 false true true)
    (Modules.Add.certification 3 5 false true true).stateCorresponds :=
  Modules.Add.implements_contract 3 5 false true true

-- Unequal unsigned operands grow to the wider width plus one.
#guard BitVector.toBitVec 6
    (outputs 3 5 false false true (bits 3 7) (bits 5 17) .result) ==
  BitVec.ofInt 6 24

-- Static signedness controls interpretation independently for each operand.
#guard BitVector.toBitVec 5
    (outputs 4 3 true false true (bits 4 (-3)) (bits 3 5) .result) ==
  BitVec.ofInt 5 2

#guard BitVector.toBitVec 5
    (outputs 4 3 true true true (bits 4 (-3)) (bits 3 (-2)) .result) ==
  BitVec.ofInt 5 (-5)

-- A non-extended result wraps at the wider input width.
#guard BitVector.toBitVec 4
    (outputs 4 4 false false false (bits 4 15) (bits 4 3) .result) ==
  BitVec.ofInt 4 18

-- Extending two empty operands still gives the single zero carry position.
#guard BitVector.toBitVec 1
    (outputs 0 0 false false true (bits 0 0) (bits 0 0) .result) ==
  BitVec.ofInt 1 0

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

#guard match renderRootModule (Modules.Add.naming 3 5 false true true) with
  | .error _ => false
  | .ok text =>
      ["public module Add_3_5_false_true_true",
       "input left : UInt<1>[3]", "input right : UInt<1>[5]",
       "output result : UInt<1>[6]", "inst add_with_carry_0"].all
        (contains text) && !contains text "input subtract"

end SileanTests.Add
