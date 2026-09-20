import Silean.FIRRTL
import Silean.Modules.CarrySaveAdder.CarrySaveAdderDerived

namespace SileanTests.CarrySaveAdder

open Silean Silean.FIRRTL

def bits (width value : Nat) : Fin width → Bool :=
  BitVector.ofNat width value

def inputs (width : Nat) (iA iB iC : Fin width → Bool) :
    (Modules.CarrySaveAdder.ports width).inputs.Values
  | .iA => iA
  | .iB => iB
  | .iC => iC

def outputs (width : Nat) (iA iB iC : Fin width → Bool) :=
  ((Modules.CarrySaveAdder.cycleContract width).evaluate
    (inputs width iA iB iC) SignalMap.emptyValues).1

-- The empty-width boundary is total and denotes zero.
#guard BitVector.toNat 0 (outputs 0 (bits 0 0) (bits 0 0) (bits 0 0) .sum) == 0
#guard BitVector.toNat 0
  (outputs 0 (bits 0 0) (bits 0 0) (bits 0 0) .carry) == 0

-- At width one, 1 + 1 + 1 produces sum bit one; the carry is truncated.
#guard BitVector.toNat 1 (outputs 1 (bits 1 1) (bits 1 1) (bits 1 1) .sum) == 1
#guard BitVector.toNat 1
  (outputs 1 (bits 1 1) (bits 1 1) (bits 1 1) .carry) == 0

-- At width four, 9 + 6 + 7 is represented as 8 + 14.
#guard BitVector.toNat 4 (outputs 4 (bits 4 9) (bits 4 6) (bits 4 7) .sum) == 8
#guard BitVector.toNat 4
  (outputs 4 (bits 4 9) (bits 4 6) (bits 4 7) .carry) == 14

example (width : Nat) (iA iB iC : Fin width → Bool) :
    (BitVector.toNat width (outputs width iA iB iC .sum) +
        BitVector.toNat width (outputs width iA iB iC .carry)) %
        BitVector.cardinality width =
      (BitVector.toNat width iA + BitVector.toNat width iB +
        BitVector.toNat width iC) % BitVector.cardinality width := by
  exact Modules.CarrySaveAdder.numeric_value_of_allowed width
    ((Modules.CarrySaveAdder.cycleContract width).evaluateStep_allowed
      (inputs width iA iB iC) SignalMap.emptyValues)

noncomputable example : Contracts.Cycle.ModuleCycleCertified
    (Modules.CarrySaveAdder.ports 0) :=
  Modules.CarrySaveAdder.certified 0

noncomputable example : Contracts.Cycle.ModuleCycleCertified
    (Modules.CarrySaveAdder.ports 1) :=
  Modules.CarrySaveAdder.certified 1

noncomputable example : Contracts.Cycle.ModuleCycleCertified
    (Modules.CarrySaveAdder.ports 4) :=
  Modules.CarrySaveAdder.certified 4

example : (Modules.CarrySaveAdder.moduleStructure 0).HasNoBlackboxes := by
  native_decide

example : (Modules.CarrySaveAdder.moduleStructure 1).HasNoBlackboxes := by
  native_decide

example : (Modules.CarrySaveAdder.moduleStructure 4).HasNoBlackboxes := by
  native_decide

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def occurrences (text fragment : String) : Nat :=
  (text.splitOn fragment).length - 1

private def rendersWithAdderCount (width expected : Nat)
    (fragments : List String) : Bool :=
  match renderRootModule (Modules.CarrySaveAdder.naming width) with
  | .error _ => false
  | .ok text => fragments.all (contains text) &&
      occurrences text "inst full_adder_" == expected

#guard rendersWithAdderCount 0 0
  ["public module CarrySaveAdder_0", "input iA : UInt<1>[0]",
   "input iB : UInt<1>[0]", "input iC : UInt<1>[0]",
   "output sum : UInt<1>[0]", "output carry : UInt<1>[0]",
   "inst combiner_0", "inst combiner_1", "inst vector_layout_0"]

#guard rendersWithAdderCount 1 1
  ["public module CarrySaveAdder_1", "inst full_adder_0 of FullAdder",
   "connect full_adder_0.left, splitter_0.component_0",
   "connect combiner_1.component_0, full_adder_0.carryOut"]

#guard rendersWithAdderCount 4 4
  ["public module CarrySaveAdder_4", "inst full_adder_0 of FullAdder",
   "inst full_adder_3 of FullAdder",
   "connect full_adder_3.carryIn, splitter_2.component_3",
   "connect combiner_0.component_3, full_adder_3.sum",
   "connect vector_layout_0.input, combiner_1.aggregate_0"]

#guard match renderClosedCircuit (Modules.CarrySaveAdder.naming 4) with
  | .error _ => false
  | .ok text => contains text "public module CarrySaveAdder_4" &&
      contains text "module FullAdder"

end SileanTests.CarrySaveAdder
