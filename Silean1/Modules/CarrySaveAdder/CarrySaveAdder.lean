import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Foundation.BitVector

/-! # Carry-save adder

`CarrySaveAdder` compresses three equal-width vectors into an unshifted sum
vector and a shifted carry vector. The contract is independent of the indexed
full-adder implementation under `Internal/`.
-/

namespace Silean.Modules.CarrySaveAdder

open Silean

module_ports ports (width : Nat) where
  input iA : .vector width .bit,
  input iB : .vector width .bit,
  input iC : .vector width .bit,
  output sum : .vector width .bit,
  output carry : .vector width .bit

/-- The parity bit produced by adding three Boolean inputs. -/
def sumBit (iA iB iC : Bool) : Bool :=
  (iA != iB) != iC

/-- Whether at least two of three Boolean inputs are set. -/
def carryBit (iA iB iC : Bool) : Bool :=
  (iA && iB) || (iA && iC) || (iB && iC)

/-- Apply the one-bit sum independently at every vector position. -/
def sumValue (width : Nat) (iA iB iC : Fin width → Bool) :
    Fin width → Bool :=
  fun index => sumBit (iA index) (iB index) (iC index)

/-- Shift each one-bit carry into the next vector position. Position zero is
zero, and a carry beyond the fixed width is discarded. -/
def carryValue (width : Nat) (iA iB iC : Fin width → Bool) :
    Fin width → Bool :=
  fun index =>
    if nonzero : 0 < index.val then
      let previous : Fin width := ⟨index.val - 1, by omega⟩
      carryBit (iA previous) (iB previous) (iC previous)
    else
      false

/-- The ordinary natural-number sum of the three input vectors. -/
def totalValue (width : Nat) (iA iB iC : Fin width → Bool) : Nat :=
  BitVector.toNat width iA + BitVector.toNat width iB +
    BitVector.toNat width iC

module_cycle_contract cycleContract (width : Nat) for ports width where
  state := emptySignalMap
  output_rule apply where
    reads := [iA, iB, iC]
    writes := {
      sum := sumValue width iA iB iC,
      carry := carryValue width iA iB iC }
  state_rule where
    reads := []
    next := {}

end Silean.Modules.CarrySaveAdder
