import Silean.FIRRTL
import Silean.Modules.SignedRoundShift.SignedRoundShiftDerived

namespace SileanTests.SignedRoundShift

open Silean Silean.FIRRTL
open Silean.Modules.SignedRoundShift

noncomputable example (retainedWidth discardedWidth : Nat) :
    Contracts.Cycle.ModuleCycleCertified
      (ports retainedWidth discardedWidth) :=
  certified retainedWidth discardedWidth

example (retainedWidth discardedWidth : Nat) :
    Contracts.Cycle.Implements
      (moduleStructure retainedWidth discardedWidth)
      (cycleContract retainedWidth discardedWidth)
      (certification retainedWidth discardedWidth).stateCorresponds :=
  implements_contract retainedWidth discardedWidth

example (retainedWidth discardedWidth : Nat)
    {step : (moduleStructure retainedWidth discardedWidth).Step}
    (realizes :
      (moduleStructure retainedWidth discardedWidth).Realizes step) :
    step.outputs .result =
      resultValue retainedWidth discardedWidth (step.inputs .value) :=
  result_of_realization retainedWidth discardedWidth realizes

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def occurrences (text fragment : String) : Nat :=
  (text.splitOn fragment).length - 1

private def rootHasShape (retainedWidth discardedWidth : Nat)
    (fragments : List String) : Bool :=
  match renderRootModule (naming retainedWidth discardedWidth) with
  | .error _ => false
  | .ok text => fragments.all (contains text) &&
      occurrences text "inst vector_slice_0" == 1 &&
      occurrences text "inst vector_layout_" == 3 &&
      occurrences text "inst splitter_" == 3 &&
      occurrences text "inst any_0" == 1 &&
      occurrences text "inst increment_0" == 1 &&
      occurrences text "inst mux_0" == 1

#guard rootHasShape 4 4
  ["public module SignedRoundShift_4_4",
   "input value : UInt<1>[8]", "output result : UInt<1>[4]",
   "connect increment_0.value, vector_slice_0.result",
   "connect mux_0.whenFalse, vector_slice_0.result",
   "connect mux_0.whenTrue, increment_0.result"]

#guard match renderCircuit (naming 4 4) with
  | .error _ => false
  | .ok text => contains text "public module SignedRoundShift_4_4" &&
      contains text "module increment_structural_4" &&
      contains text "module Mux_v4_bit"

end SileanTests.SignedRoundShift
