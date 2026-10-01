import HTFFT.Silean.FinalReorder.Control.Control
import Silean.Composition.SignalLogic

/-! Arithmetic consequences of the final-reorder controller's bit-level
address functions. -/

namespace HTFFT.Silean.FinalReorder.Control

open _root_.Silean

theorem toNat_writeAddress0 (addressWidth : Nat)
    (positive : 0 < addressWidth) (address : Address addressWidth) :
    BitVector.toNat addressWidth (writeAddress0 addressWidth address) =
      (lowBit addressWidth address).toNat *
          BitVector.cardinality (addressWidth - 1) +
        BitVector.toNat addressWidth address / 2 := by
  cases addressWidth with
  | zero => omega
  | succ width =>
      rw [BitVector.toNat]
      rw [BitVector.toNat_succ_low] at *
      simp only [writeAddress0, lowBit]
      simp
      have tail :
          (fun index : Fin width => address ⟨index.val + 1, by omega⟩) =
            (fun index : Fin width => address index.succ) := by
        funext index
        rfl
      rw [tail]
      cases address 0 <;> simp <;> omega

theorem toNat_writeAddress1 (addressWidth : Nat)
    (positive : 0 < addressWidth) (address : Address addressWidth) :
    BitVector.toNat addressWidth (writeAddress1 addressWidth address) =
      (!lowBit addressWidth address).toNat *
          BitVector.cardinality (addressWidth - 1) +
        BitVector.toNat addressWidth address / 2 := by
  cases addressWidth with
  | zero => omega
  | succ width =>
      rw [BitVector.toNat]
      rw [BitVector.toNat_succ_low] at *
      simp only [writeAddress1, lowBit]
      simp
      have tail :
          (fun index : Fin width => address ⟨index.val + 1, by omega⟩) =
            (fun index : Fin width => address index.succ) := by
        funext index
        rfl
      rw [tail]
      cases address 0 <;> simp <;> omega

@[simp] theorem lowBit_ofNat (addressWidth value : Nat)
    (positive : 0 < addressWidth) :
    lowBit addressWidth (BitVector.ofNat addressWidth value) =
      decide (value % 2 = 1) := by
  simp [lowBit, positive, BitVector.ofNat, Nat.testBit_zero]

theorem highBit_ofNat (addressWidth value : Nat)
    (positive : 0 < addressWidth)
    (bound : value < BitVector.cardinality addressWidth) :
    highBit addressWidth (BitVector.ofNat addressWidth value) =
      decide (BitVector.cardinality (addressWidth - 1) ≤ value) := by
  cases addressWidth with
  | zero => omega
  | succ width =>
      simp only [highBit, BitVector.ofNat]
      rw [show width + 1 - 1 = width by omega]
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
      rw [BitVector.cardinality_eq_pow] at bound ⊢
      have quotientBound : value / 2 ^ width < 2 := by
        apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos width)).2
        simpa [Nat.pow_succ, Nat.mul_comm] using bound
      have nonnegative : 0 ≤ value / 2 ^ width := Nat.zero_le _
      have quotientCases : value / 2 ^ width = 0 ∨
          value / 2 ^ width = 1 := by omega
      rcases quotientCases with quotientZero | quotientOne
      · simp [quotientZero]
        exact (Nat.div_eq_zero_iff_lt
          (Nat.two_pow_pos width)).mp quotientZero
      · simp [quotientOne]
        exact Nat.le_of_not_gt fun less => by
          have zero : value / 2 ^ width = 0 := Nat.div_eq_of_lt less
          omega

@[simp] theorem toNat_lastAddress (addressWidth : Nat) :
    BitVector.toNat addressWidth (lastAddress addressWidth) =
      BitVector.cardinality addressWidth - 1 := by
  induction addressWidth with
  | zero => rfl
  | succ width induction =>
      rw [BitVector.toNat]
      change BitVector.cardinality width +
          BitVector.toNat width (lastAddress width) = _
      rw [induction]
      have positive : 0 < BitVector.cardinality width := by
        rw [BitVector.cardinality_eq_pow]
        exact Nat.two_pow_pos width
      simp only [BitVector.cardinality]
      omega

theorem bypass_ofNat_eq_true_iff (addressWidth value : Nat)
    (bound : value < BitVector.cardinality addressWidth) :
    bypass addressWidth (BitVector.ofNat addressWidth value) = true ↔
      value = BitVector.cardinality addressWidth - 1 := by
  rw [bypass, SignalType.equal_eq_true_iff]
  constructor
  · intro equal
    have numeric := congrArg (BitVector.toNat addressWidth) equal
    rw [BitVector.toNat_ofNat, Nat.mod_eq_of_lt bound,
      toNat_lastAddress] at numeric
    exact numeric
  · intro equal
    apply BitVector.toNat_injective addressWidth
    rw [BitVector.toNat_ofNat, Nat.mod_eq_of_lt bound,
      toNat_lastAddress, equal]

theorem bypass_ofNat (addressWidth value : Nat)
    (bound : value < BitVector.cardinality addressWidth) :
    bypass addressWidth (BitVector.ofNat addressWidth value) =
      decide (value = BitVector.cardinality addressWidth - 1) := by
  apply Bool.eq_iff_iff.mpr
  rw [bypass_ofNat_eq_true_iff addressWidth value bound]
  simp

end HTFFT.Silean.FinalReorder.Control
