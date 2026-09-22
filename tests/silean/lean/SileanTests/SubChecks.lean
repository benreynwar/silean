import Silean.FIRRTL
import Silean.Modules.Sub.SubDerived

namespace SileanTests.Sub

open Silean Silean.FIRRTL

def bits (width : Nat) (value : Int) : Fin width → Bool :=
  BitVector.ofBitVec (BitVec.ofInt width value)

def inputs (leftWidth rightWidth : Nat)
    (leftSigned rightSigned extendOutput : Bool)
    (left : Fin leftWidth → Bool) (right : Fin rightWidth → Bool) :
    (Modules.Sub.ports leftWidth rightWidth leftSigned rightSigned
      extendOutput).inputs.Values
  | .left => left
  | .right => right

def outputs (leftWidth rightWidth : Nat)
    (leftSigned rightSigned extendOutput : Bool)
    (left : Fin leftWidth → Bool) (right : Fin rightWidth → Bool) :=
  ((Modules.Sub.cycleContract leftWidth rightWidth leftSigned rightSigned
    extendOutput).evaluate
      (inputs leftWidth rightWidth leftSigned rightSigned extendOutput left right)
      SignalMap.emptyValues).1

noncomputable example : Contracts.Cycle.ModuleCycleCertified
    (Modules.Sub.ports 4 3 true false true) :=
  Modules.Sub.certified 4 3 true false true

example : Contracts.Cycle.Implements
    (Modules.Sub.moduleStructure 4 3 true false true)
    (Modules.Sub.cycleContract 4 3 true false true)
    (Modules.Sub.certification 4 3 true false true).stateCorresponds :=
  Modules.Sub.implements_contract 4 3 true false true

-- Signed left minus unsigned right is ordinary integer subtraction.
#guard BitVector.toBitVec 5
    (outputs 4 3 true false true (bits 4 (-3)) (bits 3 5) .result) ==
  BitVec.ofInt 5 (-8)

-- Truncating subtraction wraps in the wider input width.
#guard BitVector.toBitVec 4
    (outputs 4 4 false false false (bits 4 3) (bits 4 5) .result) ==
  BitVec.ofInt 4 (-2)

-- Independent widths and signedness also work on the right operand.
#guard BitVector.toBitVec 6
    (outputs 2 5 false true true (bits 2 3) (bits 5 (-7)) .result) ==
  BitVec.ofInt 6 10

#guard BitVector.toBitVec 1
    (outputs 0 0 true true true (bits 0 0) (bits 0 0) .result) ==
  BitVec.ofInt 1 0

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

#guard match renderRootModule (Modules.Sub.naming 4 3 true false true) with
  | .error _ => false
  | .ok text =>
      ["public module Sub_4_3_true_false_true",
       "input left : UInt<1>[4]", "input right : UInt<1>[3]",
       "output result : UInt<1>[5]", "inst add_sub_with_carry_0"].all
        (contains text) && !contains text "input subtract"

end SileanTests.Sub
