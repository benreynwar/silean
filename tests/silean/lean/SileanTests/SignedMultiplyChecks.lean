import Silean.FIRRTL
import Silean.Modules.SignedMultiply.SignedMultiplyDerived

namespace SileanTests.SignedMultiply

open Silean Silean.FIRRTL
open Silean.Modules.SignedMultiply

noncomputable example (leftWidth rightWidth : Nat) :
    Contracts.Cycle.ModuleCycleCertified (ports leftWidth rightWidth) :=
  certified leftWidth rightWidth

example (leftWidth rightWidth : Nat) :
    Contracts.Cycle.Implements (moduleStructure leftWidth rightWidth)
      (cycleContract leftWidth rightWidth)
      (certification leftWidth rightWidth).stateCorresponds :=
  implements_contract leftWidth rightWidth

example (leftWidth rightWidth : Nat)
    {step : (moduleStructure leftWidth rightWidth).Step}
    (realizes : (moduleStructure leftWidth rightWidth).Realizes step) :
    (BitVector.toBitVec (leftWidth + rightWidth)
      (step.outputs .result)).toInt =
      (BitVector.toBitVec leftWidth (step.inputs .left)).toInt *
        (BitVector.toBitVec rightWidth (step.inputs .right)).toInt :=
  result_toInt_of_realization leftWidth rightWidth realizes

example : (moduleStructure 0 0).HasNoBlackboxes := by native_decide
example : (moduleStructure 0 4).HasNoBlackboxes := by native_decide
example : (moduleStructure 4 0).HasNoBlackboxes := by native_decide
example : (moduleStructure 4 3).HasNoBlackboxes := by native_decide
example : (moduleStructure 3 5).HasNoBlackboxes := by native_decide

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def occurrences (text fragment : String) : Nat :=
  (text.splitOn fragment).length - 1

private def rootHasShape (leftWidth rightWidth : Nat)
    (fragments : List String) : Bool :=
  match renderRootModule (naming leftWidth rightWidth) with
  | .error _ => false
  | .ok text => fragments.all (contains text) &&
      occurrences text "inst vector_layout_" == 2 &&
      occurrences text "inst splitter_" == 2 &&
      occurrences text "inst conditional_negate_" == 3 &&
      occurrences text "inst xor_" == 1 &&
      occurrences text "inst unsigned_multiply_" == 1

#guard rootHasShape 0 0
  ["public module SignedMultiply_0_0",
   "input left : UInt<1>[0]", "input right : UInt<1>[0]",
   "output result : UInt<1>[0]",
   "connect conditional_negate_0.negate, splitter_0.component_0",
   "connect conditional_negate_2.negate, productNegate"]

#guard rootHasShape 4 3
  ["public module SignedMultiply_4_3",
   "input left : UInt<1>[4]", "input right : UInt<1>[3]",
   "output result : UInt<1>[7]",
   "inst conditional_negate_0 of ConditionalNegate_4",
   "inst conditional_negate_1 of ConditionalNegate_3",
   "inst unsigned_multiply_0 of UnsignedMultiply_4_3",
   "inst conditional_negate_2 of ConditionalNegate_7",
   "connect unsigned_multiply_0.left, conditional_negate_0.result",
   "connect conditional_negate_2.value, unsigned_multiply_0.result"]

#guard match renderClosedCircuit (naming 4 3) with
  | .error _ => false
  | .ok text => contains text "public module SignedMultiply_4_3" &&
      contains text "module ConditionalNegate_4" &&
      contains text "module UnsignedMultiply_4_3" &&
      contains text "module carry_save_tree_recursive_7_3" &&
      contains text "module FullAdder"

end SileanTests.SignedMultiply
