import Silean.FIRRTL
import Silean.Modules.EnabledResetCounter.EnabledResetCounterTheorems

namespace Silean.Examples.Checks.EnabledResetCounter

open Silean Silean.FIRRTL Silean.Modules.EnabledResetCounter

def bits0 : Value 0 := fun index => Fin.elim0 index

def bits3Two : Value 3
  | 0 => false
  | 1 => true
  | 2 => false

def bits3Six : Value 3
  | 0 => false
  | 1 => true
  | 2 => true

def bits3Seven : Value 3 := fun _ => true

def inputs (width : Nat) (enable reset : Bool) :
    (ports width).inputs.Values
  | .enable => enable
  | .reset => reset

def state (width : Nat) (stored : Value width) :
    (Modules.Register.stateMap (valueType width)).Values
  | .stored => stored

def next (width : Nat) (resetValue stored : Value width)
    (enable reset : Bool) : Value width :=
  ((cycleContract width resetValue).evaluate
    (inputs width enable reset) (state width stored)).2 .stored

/-! The public Step theorem states the same enabled transition without
unpacking the four pieces of a cycle by hand. -/

example :
    ((cycleContract 3 bits3Two).evaluateStep
      (inputs 3 true false) (state 3 bits3Six)).nextState .stored =
      Modules.Increment.incrementValue 3 bits3Six := by
  apply next_stored_of_enabled
    ((cycleContract 3 bits3Two).evaluateStep_allowed _ _)
  · rfl
  · rfl

-- Reset has priority over an enabled increment.
#guard BitVector.toNat 3 (next 3 bits3Two bits3Seven true true) == 2
-- Disabled counters retain their complete value.
#guard BitVector.toNat 3 (next 3 bits3Two bits3Six false false) == 6
-- Enabled counters propagate carry through multiple LSB-first bits.
#guard BitVector.toNat 3 (next 3 bits3Two bits3Six true false) == 7
-- Increment wraps modulo the vector width.
#guard BitVector.toNat 3 (next 3 bits3Two bits3Seven true false) == 0
-- Width zero has one empty value and remains well-defined in every mode.
#guard BitVector.toNat 0 (next 0 bits0 bits0 true false) == 0
#guard BitVector.toNat 0 (next 0 bits0 bits0 true true) == 0

noncomputable example : Contracts.Cycle.ModuleCycleCertified (ports 0) := certified 0 bits0
noncomputable example : Contracts.Cycle.ModuleCycleCertified (ports 3) := certified 3 bits3Two

/-! The readable feedback circuit is the certified production hierarchy, and
that hierarchy implements the cycle contract used by the Step laws above. -/

example : Authoring.CircuitDescription.Corresponds
    (Description.description 3 bits3Two) (naming 3 bits3Two) :=
  Description.authored_definition_corresponds 3 bits3Two

example : Contracts.Cycle.Implements
    (moduleStructure 3 bits3Two) (cycleContract 3 bits3Two)
    (certification 3 bits3Two).stateCorresponds :=
  implements_contract 3 bits3Two

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

private def renders (width : Nat) (resetValue : Value width)
    (fragments : List String) : Bool :=
  match renderCircuit (naming width resetValue) with
  | .error _ => false
  | .ok text => fragments.all (contains text)

#guard renders 3 bits3Two
  ["public module EnabledResetCounter_3_0_1_0",
   "input enable : UInt<1>", "input reset : UInt<1>",
   "output value : UInt<1>[3]",
   "inst increment of increment_structural_3",
   "inst storage of EnabledResetRegister_v3_bit_0_1_0",
   "connect increment.value, storage.value_out",
   "connect storage.value, increment.result"]

#guard renders 0 bits0
  ["public module EnabledResetCounter_0",
   "output value : UInt<1>[0]",
   "inst increment of increment_structural_0"]

end Silean.Examples.Checks.EnabledResetCounter
