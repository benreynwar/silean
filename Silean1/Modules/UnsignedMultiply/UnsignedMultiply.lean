import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Foundation.BitVector

/-! # Full-width unsigned multiplication

`UnsignedMultiply` multiplies independently sized unsigned, least-significant-
bit-first vectors. The result width is the sum of the operand widths, so the
ordinary natural-number product is represented exactly rather than modulo a
smaller machine width. This file contains only the public boundary and
mathematical contract; the structure and its proof live in the corresponding
`Internal/` files and are exposed through `UnsignedMultiplyDerived`.
-/

namespace Silean.Modules.UnsignedMultiply

open Silean
open Silean.Authoring

module_ports ports (leftWidth : Nat) (rightWidth : Nat) where
  input left : .vector leftWidth .bit,
  input right : .vector rightWidth .bit,
  output result : .vector (leftWidth + rightWidth) .bit

/-- The exact full-width bit-vector representation of the unsigned product. -/
def resultValue (leftWidth rightWidth : Nat)
    (left : Fin leftWidth → Bool) (right : Fin rightWidth → Bool) :
    Fin (leftWidth + rightWidth) → Bool :=
  BitVector.ofNat (leftWidth + rightWidth)
    (BitVector.toNat leftWidth left * BitVector.toNat rightWidth right)

module_cycle_contract cycleContract (leftWidth : Nat) (rightWidth : Nat)
    for ports leftWidth rightWidth where
  state := emptySignalMap
  output_rule apply where
    reads := [left, right]
    writes := {
      result := resultValue leftWidth rightWidth left right }
  state_rule where
    reads := []
    next := {}

/-- The product of two decoded operands always fits in the combined width. -/
theorem product_lt_cardinality (leftWidth rightWidth : Nat)
    (left : Fin leftWidth → Bool) (right : Fin rightWidth → Bool) :
    BitVector.toNat leftWidth left * BitVector.toNat rightWidth right <
      BitVector.cardinality (leftWidth + rightWidth) := by
  have leftBound := BitVector.toNat_lt_cardinality leftWidth left
  have rightBound := BitVector.toNat_lt_cardinality rightWidth right
  rw [BitVector.cardinality_eq_pow] at leftBound rightBound ⊢
  calc
    BitVector.toNat leftWidth left * BitVector.toNat rightWidth right <
        2 ^ leftWidth * 2 ^ rightWidth :=
      Nat.mul_lt_mul_of_lt_of_le leftBound (Nat.le_of_lt rightBound)
        (Nat.pow_pos (by omega))
    _ = 2 ^ (leftWidth + rightWidth) := (Nat.pow_add 2 leftWidth rightWidth).symm

/-- The pure result function represents the product exactly. -/
theorem toNat_resultValue (leftWidth rightWidth : Nat)
    (left : Fin leftWidth → Bool) (right : Fin rightWidth → Bool) :
    BitVector.toNat (leftWidth + rightWidth)
        (resultValue leftWidth rightWidth left right) =
      BitVector.toNat leftWidth left * BitVector.toNat rightWidth right := by
  rw [resultValue, BitVector.toNat_ofNat, Nat.mod_eq_of_lt]
  exact product_lt_cardinality leftWidth rightWidth left right

/-- Decoding the specified result gives ordinary natural-number
multiplication, with no truncation or wraparound. -/
theorem result_toNat_of_allowed (leftWidth rightWidth : Nat)
    {step : (cycleContract leftWidth rightWidth).Step}
    (allowed : (cycleContract leftWidth rightWidth).Allows step) :
    BitVector.toNat (leftWidth + rightWidth) (step.outputs .result) =
      BitVector.toNat leftWidth (step.inputs .left) *
        BitVector.toNat rightWidth (step.inputs .right) := by
  rw [cycleContract.result leftWidth rightWidth allowed, toNat_resultValue]

/-- A zero-width left operand denotes zero, hence so does the full result. -/
@[simp] theorem resultValue_zero_left (rightWidth : Nat)
    (left : Fin 0 → Bool) (right : Fin rightWidth → Bool) :
    resultValue 0 rightWidth left right =
      BitVector.ofNat (0 + rightWidth) 0 := by
  simp [resultValue, BitVector.toNat]

/-- A zero-width right operand denotes zero, hence so does the full result. -/
@[simp] theorem resultValue_zero_right (leftWidth : Nat)
    (left : Fin leftWidth → Bool) (right : Fin 0 → Bool) :
    resultValue leftWidth 0 left right = BitVector.ofNat leftWidth 0 := by
  simp [resultValue, BitVector.toNat]

end Silean.Modules.UnsignedMultiply
