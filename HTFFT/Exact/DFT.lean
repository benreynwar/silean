import HTFFT.Exact.Radix2
import Mathlib.Tactic

open scoped BigOperators

namespace HTFFT.Exact

/-- The scalar multiplying input `j` at output `k` in a depth-`depth` forward
DFT. Natural arguments make the radix-two identities independent of dependent
index casts; both arguments are interpreted modulo `2^depth`. -/
noncomputable def fourierCoefficient (depth j k : Nat) : ℂ :=
  ZMod.stdAddChar
    (-((j : ZMod (2 ^ depth)) * (k : ZMod (2 ^ depth))))

theorem fourierCoefficient_eq_exp (depth j k : Nat) :
    fourierCoefficient depth j k =
      Complex.exp (-(2 * Real.pi * Complex.I * (j * k) / (2 ^ depth))) := by
  rw [fourierCoefficient]
  rw [show -((j : ZMod (2 ^ depth)) * (k : ZMod (2 ^ depth))) =
      ((-(j * k) : Int) : ZMod (2 ^ depth)) by norm_num]
  rw [ZMod.stdAddChar_coe]
  push_cast
  congr 1
  ring

/-- An even input index uses the coefficient from the half-size transform. -/
theorem fourierCoefficient_even (depth j k : Nat) :
    fourierCoefficient (depth + 1) (2 * j) k =
      fourierCoefficient depth j k := by
  rw [fourierCoefficient_eq_exp, fourierCoefficient_eq_exp]
  congr 1
  rw [show depth + 1 = depth.succ by omega, pow_succ]
  push_cast
  field_simp [pow_ne_zero]

/-- An odd input index contributes one full-size twiddle in addition to its
half-size coefficient. -/
theorem fourierCoefficient_odd (depth j k : Nat) :
    fourierCoefficient (depth + 1) (2 * j + 1) k =
      fourierCoefficient (depth + 1) 1 k *
        fourierCoefficient depth j k := by
  rw [fourierCoefficient_eq_exp, fourierCoefficient_eq_exp,
    fourierCoefficient_eq_exp]
  rw [← Complex.exp_add]
  congr 1
  rw [show depth + 1 = depth.succ by omega, pow_succ]
  push_cast
  field_simp [pow_ne_zero]
  ring

/-- Moving a first-half output index into the second half does not change the
coefficient of an even input. -/
theorem fourierCoefficient_even_secondHalf (depth j k : Nat) :
    fourierCoefficient (depth + 1) (2 * j) (k + 2 ^ depth) =
      fourierCoefficient depth j k := by
  rw [fourierCoefficient_eq_exp, fourierCoefficient_eq_exp]
  apply (Complex.exp_eq_exp_iff_exists_int).2
  refine ⟨-(j : Int), ?_⟩
  rw [show depth + 1 = depth.succ by omega, pow_succ]
  push_cast
  field_simp [pow_ne_zero]
  ring

/-- Moving a first-half output index into the second half negates the
coefficient of an odd input. -/
theorem fourierCoefficient_odd_secondHalf (depth j k : Nat) :
    fourierCoefficient (depth + 1) (2 * j + 1) (k + 2 ^ depth) =
      -(fourierCoefficient (depth + 1) 1 k *
        fourierCoefficient depth j k) := by
  rw [fourierCoefficient_eq_exp, fourierCoefficient_eq_exp,
    fourierCoefficient_eq_exp]
  rw [← Complex.exp_add]
  rw [show -Complex.exp
      (-(2 * Real.pi * Complex.I * ((1 : Nat) * k) / (2 ^ (depth + 1))) +
        -(2 * Real.pi * Complex.I * (j * k) / (2 ^ depth))) =
      Complex.exp (Real.pi * Complex.I +
        (-(2 * Real.pi * Complex.I * ((1 : Nat) * k) / (2 ^ (depth + 1))) +
          -(2 * Real.pi * Complex.I * (j * k) / (2 ^ depth)))) by
        symm
        simp only [Complex.exp_add, Complex.exp_pi_mul_I]
        ring]
  apply (Complex.exp_eq_exp_iff_exists_int).2
  refine ⟨-((j : Int) + 1), ?_⟩
  rw [show depth + 1 = depth.succ by omega, pow_succ]
  push_cast
  field_simp [pow_ne_zero]
  ring

private theorem finEquiv_eq_natCast (n : Nat) [NeZero n] (k : Fin n) :
    ZMod.finEquiv n k = (k.val : ZMod n) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      apply Fin.eq_of_val_eq
      change k.val = k.val % (n + 1)
      exact (Nat.mod_eq_of_lt k.isLt).symm

theorem zmodIndexEquiv_apply (depth : Nat) (k : Fin (2 ^ depth)) :
    zmodIndexEquiv depth k = (k.val : ZMod (2 ^ depth)) := by
  exact finEquiv_eq_natCast _ _

/-- Mathlib's DFT, reindexed over the public `Fin` vector interface. -/
theorem dft_eq_sum_fourierCoefficient (depth : Nat) (input : Vector depth ℂ)
    (k : Fin (2 ^ depth)) :
    ZMod.dft (toZModVector input) (zmodIndexEquiv depth k) =
      ∑ j : Fin (2 ^ depth),
        fourierCoefficient depth j.val k.val * input j := by
  rw [ZMod.dft_apply]
  rw [← (zmodIndexEquiv depth).sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  simp only [toZModVector, Function.comp_apply, Equiv.symm_apply_apply,
    smul_eq_mul]
  rw [zmodIndexEquiv_apply, zmodIndexEquiv_apply]
  rfl

theorem twiddle_eq_fourierCoefficient (depth : Nat)
    (k : Fin (2 ^ depth)) :
    twiddle depth k = fourierCoefficient depth 1 k.val := by
  rw [twiddle, fourierCoefficient, zmodIndexEquiv_apply]
  simp

/-- One radix-two Cooley--Tukey step for outputs in the first half. -/
theorem dft_firstHalf (depth : Nat) (input : Vector (depth + 1) ℂ)
    (k : Fin (2 ^ depth)) :
    ZMod.dft (toZModVector input)
        (zmodIndexEquiv (depth + 1) (halfIndexEquiv depth (Sum.inl k))) =
      ZMod.dft (toZModVector (evens input)) (zmodIndexEquiv depth k) +
        twiddle (depth + 1) (halfIndexEquiv depth (Sum.inl k)) *
          ZMod.dft (toZModVector (odds input)) (zmodIndexEquiv depth k) := by
  rw [dft_eq_sum_fourierCoefficient, dft_eq_sum_fourierCoefficient,
    dft_eq_sum_fourierCoefficient]
  rw [sum_parity]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro j _
    rw [parityIndexEquiv_val, halfIndexEquiv_left_val]
    simp only [Fin.val_zero, zero_add]
    rw [fourierCoefficient_even]
    rfl
  · apply Finset.sum_congr rfl
    intro j _
    rw [parityIndexEquiv_val, halfIndexEquiv_left_val]
    simp only [Fin.val_one]
    rw [Nat.add_comm 1 (2 * j.val), fourierCoefficient_odd]
    rw [twiddle_eq_fourierCoefficient, halfIndexEquiv_left_val]
    simp [mul_assoc]

/-- One radix-two Cooley--Tukey step for outputs in the second half. -/
theorem dft_secondHalf (depth : Nat) (input : Vector (depth + 1) ℂ)
    (k : Fin (2 ^ depth)) :
    ZMod.dft (toZModVector input)
        (zmodIndexEquiv (depth + 1) (halfIndexEquiv depth (Sum.inr k))) =
      ZMod.dft (toZModVector (evens input)) (zmodIndexEquiv depth k) -
        twiddle (depth + 1) (halfIndexEquiv depth (Sum.inl k)) *
          ZMod.dft (toZModVector (odds input)) (zmodIndexEquiv depth k) := by
  rw [dft_eq_sum_fourierCoefficient, dft_eq_sum_fourierCoefficient,
    dft_eq_sum_fourierCoefficient]
  rw [sum_parity]
  rw [Finset.sum_add_distrib, Finset.mul_sum, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro j _
    rw [parityIndexEquiv_val, halfIndexEquiv_right_val]
    simp only [Fin.val_zero, zero_add]
    rw [Nat.add_comm (2 ^ depth) k.val,
      fourierCoefficient_even_secondHalf]
    rfl
  · apply Finset.sum_congr rfl
    intro j _
    rw [parityIndexEquiv_val, halfIndexEquiv_right_val]
    simp only [Fin.val_one]
    rw [Nat.add_comm 1 (2 * j.val), Nat.add_comm (2 ^ depth) k.val,
      fourierCoefficient_odd_secondHalf]
    rw [twiddle_eq_fourierCoefficient, halfIndexEquiv_left_val]
    simp [mul_assoc]

/-- The exact recursive radix-two FFT agrees pointwise with Mathlib's
unnormalized negative-exponent DFT. -/
theorem radix2_agreesWithDFT : Radix2AgreesWithDFT := by
  intro depth
  induction depth with
  | zero =>
      intro input k
      have : k = 0 := Fin.eq_of_val_eq (by omega)
      subst k
      rw [dft_eq_sum_fourierCoefficient]
      simp [radix2, fourierCoefficient]
  | succ depth ih =>
      intro input k
      obtain ⟨k, rfl⟩ := (halfIndexEquiv depth).surjective k
      cases k with
      | inl k =>
          rw [radix2_firstHalf, dft_firstHalf]
          rw [ih (evens input) k, ih (odds input) k]
      | inr k =>
          rw [radix2_secondHalf, dft_secondHalf]
          rw [ih (evens input) k, ih (odds input) k]

end HTFFT.Exact
