import Silean.FIRRTL
import Silean.Modules.Increment

namespace Silean.Examples.Checks.Increment

open Silean Silean.FIRRTL

noncomputable example : ModuleCycleCertified (Modules.Increment.ports 0) :=
  Modules.Increment.certified 0
noncomputable example : ModuleCycleCertified (Modules.Increment.ports 1) :=
  Modules.Increment.certified 1
noncomputable example : ModuleCycleCertified (Modules.Increment.ports 3) :=
  Modules.Increment.certified 3
noncomputable example : ModuleCycleCertified (Modules.Increment.ports 4) :=
  Modules.Increment.certified 4

def bits0 : Fin 0 → Bool := fun index => Fin.elim0 index
def bits1Zero : Fin 1 → Bool := fun | 0 => false
def bits1One : Fin 1 → Bool := fun | 0 => true
def bits3Two : Fin 3 → Bool := fun | 0 => false | 1 => true | 2 => false
def bits3Three : Fin 3 → Bool := fun | 0 => true | 1 => true | 2 => false
def bits3Seven : Fin 3 → Bool := fun _ => true
def bits4Eleven : Fin 4 → Bool := fun
  | 0 => true | 1 => true | 2 => false | 3 => true

def inputs (width : Nat) (value : Fin width → Bool) :
    (Modules.Increment.ports width).inputs.Values
  | .value => value

def result (width : Nat) (value : Fin width → Bool) :=
  ((Modules.Increment.cycleContract width).evaluate
    (inputs width value) SignalMap.emptyValues).1 .result

#guard BitVector.toNat 0 (result 0 bits0) == 0
#guard BitVector.toNat 1 (result 1 bits1Zero) == 1
#guard BitVector.toNat 1 (result 1 bits1One) == 0
#guard BitVector.toNat 3 (result 3 bits3Two) == 3
#guard BitVector.toNat 3 (result 3 bits3Three) == 4
#guard BitVector.toNat 3 (result 3 bits3Seven) == 0
#guard BitVector.toNat 4 (result 4 bits4Eleven) == 12
#guard !(result 4 bits4Eleven) 0
#guard (result 4 bits4Eleven) 2

example (width : Nat) (value : Fin width → Bool) :
    BitVector.toNat width (result width value) =
      (BitVector.toNat width value + 1) % BitVector.cardinality width := by
  simpa [result, inputs] using Modules.Increment.result_toNat_of_evaluatesTo
    width (inputs width value) SignalMap.emptyValues
    ((Modules.Increment.cycleContract width).evaluate
      (inputs width value) SignalMap.emptyValues).1
    ((Modules.Increment.cycleContract width).evaluate
      (inputs width value) SignalMap.emptyValues).2
    ((Modules.Increment.cycleContract width).evaluate_evaluatesTo
      (inputs width value) SignalMap.emptyValues)

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def renders (width : Nat) (fragments : List String) : Bool :=
  match renderCircuit (Modules.Increment.Naming.naming width) with
  | .error _ => false
  | .ok text => fragments.all (contains text)

#guard renders 0 ["public module increment_structural_0",
  "input value : UInt<1>[0]", "output result : UInt<1>[0]",
  "inst ripple of increment_ripple_base"]
#guard renders 1 ["public module increment_structural_1",
  "inst add_high of half_adder_structural",
  "connect add_high.right, increment_lower.carry_out"]
#guard renders 3 ["module increment_ripple_recursive_3",
  "inst increment_lower of increment_ripple_recursive_2",
  "connect add_high.left, split.component_2",
  "connect increment_lower.carry_in, carry_in"]
#guard renders 4 ["module increment_ripple_recursive_4",
  "inst increment_lower of increment_ripple_recursive_3",
  "connect add_high.left, split.component_3"]

end Silean.Examples.Checks.Increment
