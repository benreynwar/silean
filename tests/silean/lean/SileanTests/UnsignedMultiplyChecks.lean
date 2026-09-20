import Silean.FIRRTL
import Silean.Modules.UnsignedMultiply.UnsignedMultiplyDerived

namespace SileanTests.UnsignedMultiply

open Silean Silean.FIRRTL
open Silean.Modules.UnsignedMultiply

example (leftWidth rightWidth : Nat) :
    ModuleStructuralCertification (moduleStructure leftWidth rightWidth) :=
  structuralCertification leftWidth rightWidth

noncomputable example (leftWidth rightWidth : Nat) :
    Contracts.Cycle.ModuleCycleCertified (ports leftWidth rightWidth) :=
  certified leftWidth rightWidth

example (leftWidth rightWidth : Nat)
    {step : (moduleStructure leftWidth rightWidth).Step}
    (realizes : (moduleStructure leftWidth rightWidth).Realizes step) :
    BitVector.toNat (leftWidth + rightWidth) (step.outputs .result) =
      BitVector.toNat leftWidth (step.inputs .left) *
        BitVector.toNat rightWidth (step.inputs .right) :=
  result_toNat_of_realization leftWidth rightWidth realizes

example : (moduleStructure 0 0).HasNoBlackboxes := by native_decide
example : (moduleStructure 0 4).HasNoBlackboxes := by native_decide
example : (moduleStructure 4 0).HasNoBlackboxes := by native_decide
example : (moduleStructure 4 3).HasNoBlackboxes := by native_decide
example : (moduleStructure 3 5).HasNoBlackboxes := by native_decide

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def occurrences (text fragment : String) : Nat :=
  (text.splitOn fragment).length - 1

private def rootHasShape (leftWidth rightWidth expectedRows : Nat)
    (fragments : List String) : Bool :=
  match renderRootModule (naming leftWidth rightWidth) with
  | .error _ => false
  | .ok text => fragments.all (contains text) &&
      occurrences text "inst partial_product_row_" == expectedRows &&
      occurrences text "inst tree " == 1 &&
      occurrences text "inst add " == 1

#guard rootHasShape 0 0 0
  ["public module UnsignedMultiply_0_0",
   "input left : UInt<1>[0]", "input right : UInt<1>[0]",
   "output result : UInt<1>[0]", "inst tree of carry_save_tree_zero_0"]

#guard rootHasShape 4 0 0
  ["public module UnsignedMultiply_4_0", "output result : UInt<1>[4]",
   "inst tree of carry_save_tree_zero_4", "inst add of add_ripple_4"]

#guard rootHasShape 4 3 3
  ["public module UnsignedMultiply_4_3", "output result : UInt<1>[7]",
   "inst partial_product_row_0 of PartialProductRow_row_0_4_3",
   "inst partial_product_row_2 of PartialProductRow_row_2_4_3",
   "inst tree of carry_save_tree_recursive_7_3",
   "connect add.left, tree.resultA", "connect add.right, tree.resultB"]

#guard rootHasShape 3 5 5
  ["public module UnsignedMultiply_3_5", "output result : UInt<1>[8]",
   "inst partial_product_row_4 of PartialProductRow_row_4_3_5",
   "inst tree of carry_save_tree_recursive_8_5"]

#guard match renderClosedCircuit (naming 4 3) with
  | .error _ => false
  | .ok text => contains text "public module UnsignedMultiply_4_3" &&
      contains text "module PartialProductRow_row_0_4_3" &&
      contains text "module carry_save_tree_recursive_7_3" &&
      contains text "module add_ripple_7" &&
      contains text "module FullAdder"

end SileanTests.UnsignedMultiply
