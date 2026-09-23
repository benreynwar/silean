import Silean.FIRRTL
import Silean.Modules.ConditionalNegate.ConditionalNegateDerived

namespace SileanTests.ConditionalNegate

open Silean Silean.FIRRTL
open Silean.Modules.ConditionalNegate

noncomputable example (width : Nat) :
    Contracts.Cycle.ModuleCycleCertified (ports width) :=
  certified width

example (width : Nat) :
    Contracts.Cycle.Implements (moduleStructure width) (cycleContract width)
      (certification width).stateCorresponds :=
  implements_contract width

example (width : Nat) {step : (moduleStructure width).Step}
    (realizes : (moduleStructure width).Realizes step) :
    BitVector.toBitVec width (step.outputs .result) =
      bif step.inputs .negate then
        -BitVector.toBitVec width (step.inputs .value)
      else
        BitVector.toBitVec width (step.inputs .value) :=
  result_toBitVec_of_realization width realizes

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def occurrences (text fragment : String) : Nat :=
  (text.splitOn fragment).length - 1

private def rootHasShape (width : Nat) (fragments : List String) : Bool :=
  match renderRootModule (naming width) with
  | .error _ => false
  | .ok text => fragments.all (contains text) &&
      occurrences text "inst combiner_0" == 1 &&
      occurrences text "inst bitwise_xor_0" == 1 &&
      occurrences text "inst constant_0" == 1 &&
      occurrences text "inst add_with_carry_0" == 1

#guard rootHasShape 0
  ["public module ConditionalNegate_0",
   "input value : UInt<1>[0]", "input negate : UInt<1>",
   "output result : UInt<1>[0]",
   "connect add_with_carry_0.carry_in, negate"]

#guard rootHasShape 4
  ["public module ConditionalNegate_4",
   "input value : UInt<1>[4]", "output result : UInt<1>[4]",
   "connect bitwise_xor_0.left, value",
   "connect add_with_carry_0.left, transformedValue"]

#guard match renderCircuit (naming 4) with
  | .error _ => false
  | .ok text => contains text "public module ConditionalNegate_4" &&
      contains text "module bitwise_xor" &&
      contains text "module add_with_carry_ripple_4" &&
      contains text "module FullAdder"

end SileanTests.ConditionalNegate
