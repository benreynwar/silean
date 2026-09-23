import Silean.FIRRTL
import Silean.Foundation.BitVector
import Silean.Modules.PartialProductRow.PartialProductRowDerived

namespace SileanTests.PartialProductRow

open Silean Silean.FIRRTL

def eleven : Fin 4 → Bool := Silean.BitVector.ofNat 4 11

def inputs (select : Bool) :
    (Modules.PartialProductRow.ports 4 3).inputs.Values
  | .multiplicand => eleven
  | .select => select

def output (row : Fin 3) (select : Bool) :=
  ((Modules.PartialProductRow.cycleContract 4 3 row).evaluate
    (inputs select) SignalMap.emptyValues).1 .result

-- The selected rows for 1011 × 101 are 11, zero, and 44.
#guard Silean.BitVector.toNat 7 (output 0 true) == 11
#guard Silean.BitVector.toNat 7 (output 1 false) == 0
#guard Silean.BitVector.toNat 7 (output 2 true) == 44

example (row : Fin 3) (multiplicand : Fin 4 → Bool) (select : Bool) :
    Modules.PartialProductRow.resultNat 4 row multiplicand select =
      if select then Silean.BitVector.toNat 4 multiplicand <<< row.val else 0 :=
  rfl

noncomputable example : Contracts.Cycle.ModuleCycleCertified
    (Modules.PartialProductRow.ports 4 3) :=
  Modules.PartialProductRow.certified 4 3 2

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

#guard match renderRootModule (Modules.PartialProductRow.naming 4 3 2) with
  | .error _ => false
  | .ok text =>
      ["public module PartialProductRow_row_2_4_3",
       "input multiplicand : UInt<1>[4]", "input select : UInt<1>",
       "output result : UInt<1>[7]", "inst mask_0", "inst left_shift_0"].all
        (contains text)

end SileanTests.PartialProductRow
