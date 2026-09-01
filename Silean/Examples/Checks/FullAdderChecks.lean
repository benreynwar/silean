import Silean.FIRRTL
import Silean.Modules.FullAdder

namespace Silean.Examples.Checks.FullAdder

open Silean Silean.FIRRTL

noncomputable example : Contracts.Cycle.ModuleCycleCertified Modules.FullAdder.ports :=
  Modules.FullAdder.certified

/-- FullAdder likewise exports a proof valid for arbitrary child structures
meeting its two HalfAdder and OR boundary contracts. -/
noncomputable example := Modules.FullAdder.certifiedLayer.certify

example : ModuleStructure.NoBlackboxesCertified Modules.FullAdder.moduleStructure :=
  Modules.FullAdder.noBlackboxesCertified

/-- Clients cannot discharge the private state relation by unfolding the
FullAdder proof; they must use its public state-coverage guarantee. -/
example (structuralState : Modules.FullAdder.moduleStructure.State) :
    Modules.FullAdder.certified.certification.stateCorresponds
      SignalMap.emptyValues structuralState := by
  fail_if_success exact trivial
  rcases Modules.FullAdder.certified.certification.hasCorrespondingState
      structuralState with ⟨contractState, corresponds⟩
  rw [Subsingleton.elim SignalMap.emptyValues contractState]
  exact corresponds

def inputs (left right carryIn : Bool) : Modules.FullAdder.ports.inputs.Values
  | .left => left
  | .right => right
  | .carryIn => carryIn

def result (left right carryIn : Bool) :=
  (Modules.FullAdder.cycleContract.evaluate
    (inputs left right carryIn) SignalMap.emptyValues).1

#guard !(result false false false .sum) && !(result false false false .carryOut)
#guard result false false true .sum && !(result false false true .carryOut)
#guard result false true false .sum && !(result false true false .carryOut)
#guard !(result false true true .sum) && result false true true .carryOut
#guard result true false false .sum && !(result true false false .carryOut)
#guard !(result true false true .sum) && result true false true .carryOut
#guard !(result true true false .sum) && result true true false .carryOut
#guard result true true true .sum && result true true true .carryOut

example (left right carryIn : Bool) :
    (result left right carryIn .sum).toNat +
        2 * (result left right carryIn .carryOut).toNat =
      left.toNat + right.toNat + carryIn.toNat := by
  simpa [result, inputs] using Modules.FullAdder.numeric_value_of_evaluatesTo
    (inputs left right carryIn) SignalMap.emptyValues
    (Modules.FullAdder.cycleContract.evaluate
      (inputs left right carryIn) SignalMap.emptyValues).1
    (Modules.FullAdder.cycleContract.evaluate
      (inputs left right carryIn) SignalMap.emptyValues).2
    (Modules.FullAdder.cycleContract.evaluate_evaluatesTo
      (inputs left right carryIn) SignalMap.emptyValues)

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

#guard match renderRootModule Modules.FullAdder.Naming.naming with
  | .error _ => false
  | .ok text =>
      ["public module full_adder_structural",
       "input left : UInt<1>", "input right : UInt<1>",
       "input carry_in : UInt<1>",
       "output sum : UInt<1>", "output carry_out : UInt<1>",
       "inst operands of half_adder_structural",
       "inst carry of half_adder_structural",
       "inst combine_carry of or_bit",
       "connect carry.left, operands.sum",
       "connect combine_carry.left, operands.carry",
       "connect combine_carry.right, carry.carry"].all (contains text)

end Silean.Examples.Checks.FullAdder
