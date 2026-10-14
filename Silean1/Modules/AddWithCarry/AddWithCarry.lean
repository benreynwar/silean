import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Foundation.BitVector

/-! # Fixed-width addition with explicit carry

`AddWithCarry` computes the wrapping result and carry-out of adding two equally wide
LSB-first vectors and a carry-in. Its recursive ripple implementation is kept
under `Internal/`; this file contains only the boundary and mathematical
contract.
-/

namespace Silean.Modules.AddWithCarry

open Silean
open Silean.Authoring

module_ports ports (width : Nat) where
  input left : .vector width .bit,
  input right : .vector width .bit,
  input carryIn (name := "carry_in") : .bit,
  output result : .vector width .bit,
  output carryOut (name := "carry_out") : .bit

/-- The ordinary natural-number sum represented by the inputs. -/
def totalValue (width : Nat) (left right : Fin width → Bool)
    (carryIn : Bool) : Nat :=
  BitVector.toNat width left + BitVector.toNat width right + carryIn.toNat

/-- The low `width` bits of the natural-number sum. -/
def resultValue (width : Nat) (left right : Fin width → Bool)
    (carryIn : Bool) : Fin width → Bool :=
  BitVector.ofNat width (totalValue width left right carryIn)

/-- The bit immediately above the fixed-width result. -/
def carryValue (width : Nat) (left right : Fin width → Bool)
    (carryIn : Bool) : Bool :=
  (totalValue width left right carryIn).testBit width

module_cycle_contract cycleContract (width : Nat) for ports width where
  state := emptySignalMap
  output_rule apply where
    reads := [left, right, carryIn]
    writes := {
      result := resultValue width left right carryIn,
      carryOut := carryValue width left right carryIn }
  state_rule where
    reads := []
    next := {}

end Silean.Modules.AddWithCarry
