import Silean.FIRRTL
import Silean.Modules.RegisterBank.RegisterBankTheorems

namespace Silean.Examples.Checks.RegisterBank

open Silean Silean.FIRRTL

noncomputable example : Contracts.Cycle.ModuleCycleCertified
    (Modules.RegisterBank.ports .bit 0 1) :=
  Modules.RegisterBank.certified .bit 0 1

noncomputable example : Contracts.Cycle.ModuleCycleCertified
    (Modules.RegisterBank.ports (.vector 3 .bit) 2 2) :=
  Modules.RegisterBank.certified (.vector 3 .bit) 2 2

-- A write-only bank is also well formed; no artificial nonempty-read premise
-- is hidden in the generic construction or certification.
noncomputable example : Contracts.Cycle.ModuleCycleCertified
    (Modules.RegisterBank.ports .bit 2 0) :=
  Modules.RegisterBank.certified .bit 2 0

def address (value : Fin 4) : Fin 2 → Bool
  | 0 => value.val % 2 = 1
  | 1 => value.val / 2 % 2 = 1

def inputs (writeEnable : Bool) (writeAddress : Fin 4)
    (writeValue : Bool) (readAddress : Fin 4) :
    (Modules.RegisterBank.ports .bit 2 1).inputs.Values
  | .writeEnable => writeEnable
  | .writeAddress => address writeAddress
  | .writeValue => writeValue
  | .readAddress 0 => address readAddress

def initialState : (Modules.RegisterBank.stateMap .bit 2).Values
  | .entries => fun | 0 => false | 1 => true | 2 => false | 3 => true

def sameAddressCycle := (Modules.RegisterBank.cycleContract .bit 2 1).evaluate
  (inputs true 1 false 1) initialState

def sameAddressStep := (Modules.RegisterBank.cycleContract .bit 2 1).evaluateStep
  (inputs true 1 false 1) initialState

-- Combinational read observes the pre-update value; the write appears in next state.
#guard sameAddressCycle.1 (.readValue 0)
#guard !(sameAddressCycle.2 .entries 1)
#guard sameAddressCycle.2 .entries 3

-- The reader-facing Step laws capture the two important timing facts: reads
-- see the current array, while an enabled write changes the next array.
example : sameAddressStep.outputs (.readValue 0) =
    sameAddressStep.currentState .entries
      (BitVector.toIndex 2 (sameAddressStep.inputs (.readAddress 0))) := by
  exact Modules.RegisterBank.readValue_of_allowed
    ((Modules.RegisterBank.cycleContract .bit 2 1).evaluateStep_allowed _ _) 0

example : sameAddressStep.nextState .entries
      (BitVector.toIndex 2 (sameAddressStep.inputs .writeAddress)) =
    sameAddressStep.inputs .writeValue := by
  apply Modules.RegisterBank.written_entry_of_allowed
    ((Modules.RegisterBank.cycleContract .bit 2 1).evaluateStep_allowed _ _)
  rfl

def dualReadInputs : (Modules.RegisterBank.ports .bit 2 2).inputs.Values
  | .writeEnable => false
  | .writeAddress => address 0
  | .writeValue => false
  | .readAddress port => if port = 0 then address 1 else address 2

def dualReadCycle := (Modules.RegisterBank.cycleContract .bit 2 2).evaluate
  dualReadInputs initialState

-- Both combinational ports independently observe the shared pre-update state.
#guard dualReadCycle.1 (.readValue 0)
#guard !(dualReadCycle.1 (.readValue 1))

example : Modules.RegisterBank.entryCount 3 = 8 := by decide

example : Contracts.Cycle.Implements
    (Modules.RegisterBank.moduleStructure .bit 2 1)
    (Modules.RegisterBank.cycleContract .bit 2 1)
    (Modules.RegisterBank.certification .bit 2 1).stateCorresponds :=
  Modules.RegisterBank.implements_contract .bit 2 1

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

#guard match renderCircuit (Modules.RegisterBank.Naming.naming .bit 2 1) with
  | .error _ => false
  | .ok text => ["public module RegisterBank_bit_2_1",
      "input write_enable : UInt<1>", "input write_address : UInt<1>[2]",
      "input read_0_address : UInt<1>[2]", "output read_0_value : UInt<1>",
      "inst entry_0", "inst entry_3",
      "inst read_0_mux"].all (contains text)

#guard match renderClosedCircuit (Modules.RegisterBank.Naming.naming .bit 2 2) with
  | .error _ => false
  | .ok text => ["input read_0_address : UInt<1>[2]",
      "input read_1_address : UInt<1>[2]",
      "output read_0_value : UInt<1>", "output read_1_value : UInt<1>",
      "inst read_0_mux", "inst read_1_mux"].all (contains text)

end Silean.Examples.Checks.RegisterBank
