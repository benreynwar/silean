import Silean2.FIRRTL
import Silean2.Modules.HalfAdder

namespace Silean2.Examples.Checks.HalfAdder

open Silean2 Silean2.FIRRTL

noncomputable example : ModuleCycleCertified Modules.HalfAdder.ports :=
  Modules.HalfAdder.certified

def inputs (left right : Bool) : Modules.HalfAdder.ports.inputs.Values
  | .left => left
  | .right => right

def result (left right : Bool) :=
  (Modules.HalfAdder.cycleContract.evaluate (inputs left right) SignalMap.emptyValues).1

def sumResult (left right : Bool) : Bool := result left right .sum
def carryResult (left right : Bool) : Bool := result left right .carry

#guard !sumResult false false
#guard !carryResult false false
#guard sumResult false true
#guard !carryResult false true
#guard sumResult true false
#guard !carryResult true false
#guard !sumResult true true
#guard carryResult true true

example (left right : Bool) :
    (result left right .sum).toNat + 2 * (result left right .carry).toNat =
      left.toNat + right.toNat := by
  simpa [result, inputs] using Modules.HalfAdder.numeric_value_of_evaluatesTo
    (inputs left right) SignalMap.emptyValues
    (Modules.HalfAdder.cycleContract.evaluate
      (inputs left right) SignalMap.emptyValues).1
    (Modules.HalfAdder.cycleContract.evaluate
      (inputs left right) SignalMap.emptyValues).2
    (Modules.HalfAdder.cycleContract.evaluate_evaluatesTo
      (inputs left right) SignalMap.emptyValues)

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def containsAll (rendered : RenderResult String) (fragments : List String) : Bool :=
  match rendered with
  | .error _ => false
  | .ok text => fragments.all (contains text)

#guard containsAll (renderCircuit Silean2.Naming.Primitive.xor)
  ["public module xor_bit", "connect out, xor(left, right)"]

#guard containsAll (renderCircuit Modules.HalfAdder.Naming.naming)
  ["public module half_adder_structural",
   "input left : UInt<1>", "input right : UInt<1>",
   "output sum : UInt<1>", "output carry : UInt<1>",
   "inst sum_gate of xor_bit", "inst carry_gate of and_bit",
   "connect sum_gate.left, left", "connect carry_gate.right, right"]

end Silean2.Examples.Checks.HalfAdder
