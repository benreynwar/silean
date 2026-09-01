import Silean.FIRRTL
import Silean.Modules.HalfAdder

namespace Silean.Examples.Checks.HalfAdder

open Silean Silean.FIRRTL

noncomputable example : Contracts.Cycle.ModuleCycleCertified Modules.HalfAdder.ports :=
  Modules.HalfAdder.certified

/-- The public proof is a reusable layer certificate, not merely a proof about
the concrete XOR/AND hierarchy selected by `moduleStructure`. -/
noncomputable example := Modules.HalfAdder.certifiedLayer.certify

example : ModuleStructure.NoBlackboxesCertified Modules.HalfAdder.moduleStructure :=
  Modules.HalfAdder.noBlackboxesCertified

/-- The exported proof is intentionally opaque: clients obtain state
correspondence from its public coverage theorem, not by reducing the private
relation to `True`. -/
example (structuralState : Modules.HalfAdder.moduleStructure.State) :
    Modules.HalfAdder.certified.certification.stateCorresponds
      SignalMap.emptyValues structuralState := by
  fail_if_success exact trivial
  rcases Modules.HalfAdder.certified.certification.hasCorrespondingState
      structuralState with ⟨contractState, corresponds⟩
  rw [Subsingleton.elim SignalMap.emptyValues contractState]
  exact corresponds

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

#guard containsAll (renderCircuit Silean.Naming.Primitive.xor)
  ["public module xor_bit", "connect out, xor(left, right)"]

#guard containsAll (renderCircuit Modules.HalfAdder.Naming.naming)
  ["public module half_adder_structural",
   "input left : UInt<1>", "input right : UInt<1>",
   "output sum : UInt<1>", "output carry : UInt<1>",
   "inst sum_gate of xor_bit", "inst carry_gate of and_bit",
   "connect sum_gate.left, left", "connect carry_gate.right, right"]

end Silean.Examples.Checks.HalfAdder
