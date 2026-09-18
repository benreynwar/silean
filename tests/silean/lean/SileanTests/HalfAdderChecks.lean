import Silean.FIRRTL
import Silean.Modules.HalfAdder.HalfAdderTheorems

namespace SileanTests.HalfAdder

open Silean Silean.FIRRTL

example : Modules.HalfAdder.Description.description.children.map (·.name) =
    [.indexed "xor" 0, .indexed "and" 0] := rfl

example : Authoring.CircuitDescription.Corresponds
    Modules.HalfAdder.Description.description Modules.HalfAdder.naming :=
  Modules.HalfAdder.Description.authored_definition_corresponds

noncomputable example : Contracts.Cycle.ModuleCycleCertified Modules.HalfAdder.ports :=
  Modules.HalfAdder.certified

example : Modules.HalfAdder.sumRule.readsInputs.labels =
    [.left, .right] := rfl

example : Modules.HalfAdder.sumRule.writesOutputs.labels = [.sum] := rfl

example : Modules.HalfAdder.carryRule.readsInputs.labels =
    [.left, .right] := rfl

example : Modules.HalfAdder.carryRule.writesOutputs.labels = [.carry] := rfl

/-- The public proof is a reusable layer certificate, not merely a proof about
the concrete XOR/AND hierarchy selected by `moduleStructure`. -/
noncomputable example := Modules.HalfAdder.certifiedLayer.certify

example : ModuleStructure.NoBlackboxesCertified Modules.HalfAdder.moduleStructure :=
  Modules.HalfAdder.noBlackboxesCertified

example {step : Modules.HalfAdder.moduleStructure.Step}
    (realizes : Modules.HalfAdder.moduleStructure.Realizes step) :
    Modules.HalfAdder.Behavior step.inputs step.outputs :=
  Modules.HalfAdder.Description.behavior_of_realization realizes

example : Contracts.Cycle.Implements
    Modules.HalfAdder.moduleStructure Modules.HalfAdder.cycleContract
    Modules.HalfAdder.certification.stateCorresponds :=
  Modules.HalfAdder.implements_contract

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
  exact (Modules.HalfAdder.Behavior.of_allowed
    (Modules.HalfAdder.cycleContract.evaluateStep_allowed
      (inputs left right) SignalMap.emptyValues)).numeric_value

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def containsAll (rendered : RenderResult String) (fragments : List String) : Bool :=
  match rendered with
  | .error _ => false
  | .ok text => fragments.all (contains text)

#guard containsAll (renderCircuit Silean.Naming.Primitive.xor)
  ["public module xor_bit", "connect out, xor(left, right)"]

#guard containsAll (renderCircuit Modules.HalfAdder.design.naming)
  ["public module HalfAdder",
   "input left : UInt<1>", "input right : UInt<1>",
   "output sum : UInt<1>", "output carry : UInt<1>",
   "inst xor_0 of xor_bit", "inst and_0 of and_bit",
   "connect xor_0.left, left", "connect and_0.right, right"]

end SileanTests.HalfAdder
