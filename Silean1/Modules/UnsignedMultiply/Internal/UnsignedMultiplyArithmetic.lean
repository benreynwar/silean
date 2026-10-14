import Silean.Modules.UnsignedMultiply.Internal.UnsignedMultiplyStructure

/-! Arithmetic support for the structural unsigned multiplier proof. -/

namespace Silean.Modules.UnsignedMultiply.Internal

open Silean

/-- The ordinary natural-number sum represented by all mathematical partial
product rows. -/
def rowNatTotal (leftWidth rightWidth : Nat)
    (left : Fin leftWidth → Bool) (right : Fin rightWidth → Bool) : Nat :=
  (List.ofFn fun row =>
    PartialProductRow.resultNat leftWidth row left (right row)).sum

private theorem later_resultNat (leftWidth rightWidth : Nat)
    (left : Fin leftWidth → Bool) (right : Fin (rightWidth + 1) → Bool)
    (row : Fin rightWidth) :
    PartialProductRow.resultNat leftWidth row.succ left (right row.succ) =
      2 * PartialProductRow.resultNat leftWidth row left (right row.succ) := by
  cases selected : right row.succ <;>
    simp [PartialProductRow.resultNat, Nat.shiftLeft_eq, Nat.pow_succ,
      Nat.mul_assoc, Nat.mul_comm]

private theorem sum_ofFn_twice (count : Nat) (values : Fin count → Nat) :
    (List.ofFn fun index => 2 * values index).sum =
      2 * (List.ofFn values).sum := by
  induction count with
  | zero => simp
  | succ count induction =>
      rw [List.ofFn_succ, List.ofFn_succ]
      simp only [List.sum_cons]
      rw [induction]
      omega

/-- Summing all ordinary binary partial-product rows gives exact unsigned
multiplication. -/
theorem rowNatTotal_eq_product (leftWidth : Nat) : ∀ (rightWidth : Nat)
    (left : Fin leftWidth → Bool) (right : Fin rightWidth → Bool),
    rowNatTotal leftWidth rightWidth left right =
      BitVector.toNat leftWidth left * BitVector.toNat rightWidth right
  | 0, left, right => by
      simp [rowNatTotal, BitVector.toNat]
  | rightWidth + 1, left, right => by
      let tail := fun index : Fin rightWidth => right index.succ
      have laterFunction :
          (fun row : Fin rightWidth =>
            PartialProductRow.resultNat leftWidth row.succ left
              (right row.succ)) =
          (fun row : Fin rightWidth =>
            2 * PartialProductRow.resultNat leftWidth row left (tail row)) := by
        funext row
        exact later_resultNat leftWidth rightWidth left right row
      unfold rowNatTotal
      rw [List.ofFn_succ, List.sum_cons, laterFunction, sum_ofFn_twice]
      change PartialProductRow.resultNat leftWidth 0 left (right 0) +
          2 * rowNatTotal leftWidth rightWidth left tail = _
      rw [rowNatTotal_eq_product leftWidth rightWidth left tail]
      rw [BitVector.toNat_succ_low]
      cases selected : right 0 <;>
        simp [PartialProductRow.resultNat, tail, Nat.shiftLeft_eq,
          Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]

end Silean.Modules.UnsignedMultiply.Internal
