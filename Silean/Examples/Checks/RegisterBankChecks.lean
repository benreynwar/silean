import Silean.FIRRTL
import Silean.Modules.RegisterBank

namespace Silean.Examples.Checks.RegisterBank

open Silean Silean.FIRRTL

noncomputable example : ModuleCycleCertified
    (Modules.RegisterBank.ports .bit 0) :=
  Modules.RegisterBank.certified .bit 0

noncomputable example : ModuleCycleCertified
    (Modules.RegisterBank.ports (.vector 3 .bit) 2) :=
  Modules.RegisterBank.certified (.vector 3 .bit) 2

def address (value : Fin 4) : Fin 2 → Bool
  | 0 => value.val % 2 = 1
  | 1 => value.val / 2 % 2 = 1

def inputs (writeEnable : Bool) (writeAddress : Fin 4)
    (writeValue : Bool) (readAddress : Fin 4) :
    (Modules.RegisterBank.ports .bit 2).inputs.Values
  | .writeEnable => writeEnable
  | .writeAddress => address writeAddress
  | .writeValue => writeValue
  | .readAddress => address readAddress

def initialState : (Modules.RegisterBank.stateMap .bit 2).Values
  | .entries => fun | 0 => false | 1 => true | 2 => false | 3 => true

def sameAddressCycle := (Modules.RegisterBank.cycleContract .bit 2).evaluate
  (inputs true 1 false 1) initialState

-- Combinational read observes the pre-update value; the write appears in next state.
#guard sameAddressCycle.1 .readValue
#guard !(sameAddressCycle.2 .entries 1)
#guard sameAddressCycle.2 .entries 3

example : Modules.RegisterBank.entryCount 3 = 8 := by decide

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

#guard match renderCircuit (Modules.RegisterBank.Naming.naming .bit 2) with
  | .error _ => false
  | .ok text => ["public module register_bank_structural_bit_2",
      "input write_enable : UInt<1>", "input write_address : UInt<1>[2]",
      "output read_value : UInt<1>", "inst entry_0", "inst entry_3",
      "inst read_mux"].all (contains text)

end Silean.Examples.Checks.RegisterBank
