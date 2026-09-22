import Silean.FIRRTL
import Silean.Modules.AddSub.AddSubDerived

namespace SileanTests.AddSub

open Silean Silean.FIRRTL

def bits (width : Nat) (value : Int) : Fin width → Bool :=
  BitVector.ofBitVec (BitVec.ofInt width value)

def inputs (leftWidth rightWidth : Nat)
    (leftSigned rightSigned extendOutput : Bool)
    (left : Fin leftWidth → Bool) (right : Fin rightWidth → Bool)
    (subtract : Bool) :
    (Modules.AddSub.ports leftWidth rightWidth leftSigned rightSigned
      extendOutput).inputs.Values
  | .left => left
  | .right => right
  | .subtract => subtract

def outputs (leftWidth rightWidth : Nat)
    (leftSigned rightSigned extendOutput : Bool)
    (left : Fin leftWidth → Bool) (right : Fin rightWidth → Bool)
    (subtract : Bool) :=
  ((Modules.AddSub.cycleContract leftWidth rightWidth leftSigned rightSigned
    extendOutput).evaluate
      (inputs leftWidth rightWidth leftSigned rightSigned extendOutput left right
        subtract)
      SignalMap.emptyValues).1

noncomputable example : Contracts.Cycle.ModuleCycleCertified
    (Modules.AddSub.ports 4 3 true false true) :=
  Modules.AddSub.certified 4 3 true false true

example : Contracts.Cycle.Implements
    (Modules.AddSub.moduleStructure 4 3 true false true)
    (Modules.AddSub.cycleContract 4 3 true false true)
    (Modules.AddSub.certification 4 3 true false true).stateCorresponds :=
  Modules.AddSub.implements_contract 4 3 true false true

-- The runtime selector chooses between the same natural operations as Add/Sub.
#guard BitVector.toBitVec 5
    (outputs 4 3 true false true (bits 4 (-3)) (bits 3 5) false .result) ==
  BitVec.ofInt 5 2
#guard BitVector.toBitVec 5
    (outputs 4 3 true false true (bits 4 (-3)) (bits 3 5) true .result) ==
  BitVec.ofInt 5 (-8)

-- The selected operation wraps when output extension is disabled.
#guard BitVector.toBitVec 4
    (outputs 4 4 false false false (bits 4 15) (bits 4 3) false .result) ==
  BitVec.ofInt 4 18
#guard BitVector.toBitVec 4
    (outputs 4 4 false false false (bits 4 3) (bits 4 5) true .result) ==
  BitVec.ofInt 4 (-2)

#guard BitVector.toBitVec 0
    (outputs 0 0 true true false (bits 0 0) (bits 0 0) true .result) ==
  BitVec.ofInt 0 0

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

#guard match renderRootModule (Modules.AddSub.naming 4 3 true false true) with
  | .error _ => false
  | .ok text =>
      ["public module AddSub_4_3_true_false_true",
       "input left : UInt<1>[4]", "input right : UInt<1>[3]",
       "input subtract : UInt<1>", "output result : UInt<1>[5]",
       "inst add_sub_with_carry_0"].all (contains text)

end SileanTests.AddSub
