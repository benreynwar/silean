import HTFFT.FixedPoint.Correctness

namespace HTFFT.FixedPoint

/-- A symmetric raw-integer bound on both components of a fixed-point complex
value. This is proof bookkeeping beneath natural decoded-value bounds; it is
not a second numerical specification. -/
def ComplexBound (bound : Int) (value : HTFFT.Complex Int) : Prop :=
  |value.real| ≤ bound ∧ |value.imag| ≤ bound

theorem FitsWidth.of_abs_le_signedMax {width : Nat} {raw bound : Int}
    (rawBound : |raw| ≤ bound) (boundFits : bound ≤ signedMax width) :
    FitsWidth width raw := by
  rw [abs_le] at rawBound
  constructor
  · cases width with
    | zero =>
        change bound ≤ 0 at boundFits
        change 0 ≤ raw
        omega
    | succ width =>
        change bound ≤ ((2 ^ width : Nat) : Int) - 1 at boundFits
        change -((2 ^ width : Nat) : Int) ≤ raw
        have powerPositive : (0 : Int) < (2 ^ width : Nat) := by
          positivity
        omega
  · exact rawBound.2.trans boundFits

theorem ComplexFits.of_bound {format : Format} {value : HTFFT.Complex Int}
    {bound : Int} (valueBound : ComplexBound bound value)
    (boundFits : bound ≤ signedMax format.width) :
    ComplexFits format value := by
  exact ⟨FitsWidth.of_abs_le_signedMax valueBound.1 boundFits,
    FitsWidth.of_abs_le_signedMax valueBound.2 boundFits⟩

theorem ComplexBound.nonnegative {bound : Int} {value : HTFFT.Complex Int}
    (bounded : ComplexBound bound value) : 0 ≤ bound := by
  exact (abs_nonneg value.real).trans bounded.1

theorem ComplexBound.add {leftBound rightBound : Int}
    {left right : HTFFT.Complex Int}
    (leftBounded : ComplexBound leftBound left)
    (rightBounded : ComplexBound rightBound right) :
    ComplexBound (leftBound + rightBound) (left + right) := by
  constructor
  · exact (abs_add_le _ _).trans
      (add_le_add leftBounded.1 rightBounded.1)
  · exact (abs_add_le _ _).trans
      (add_le_add leftBounded.2 rightBounded.2)

theorem ComplexBound.sub {leftBound rightBound : Int}
    {left right : HTFFT.Complex Int}
    (leftBounded : ComplexBound leftBound left)
    (rightBounded : ComplexBound rightBound right) :
    ComplexBound (leftBound + rightBound) (left - right) := by
  constructor
  · exact (abs_sub _ _).trans
      (add_le_add leftBounded.1 rightBounded.1)
  · exact (abs_sub _ _).trans
      (add_le_add leftBounded.2 rightBounded.2)

/-- If the exact numerator is bounded by `bound * denominator`, every
supported rounding policy produces an integer of magnitude at most
`bound + 1`. The extra unit is the same conservative allowance used by the
generic numerical theorem. -/
theorem abs_roundRatio_le (mode : RoundingMode) (numerator : Int)
    (denominator : Nat) (bound : Int) (denominatorPositive : 0 < denominator)
    (_boundNonnegative : 0 ≤ bound)
    (numeratorBound : |numerator| ≤ bound * denominator) :
    |roundRatio mode numerator denominator| ≤ bound + 1 := by
  have residual := roundRatio_residual_le mode numerator denominator
    denominatorPositive
  have denominatorIntPositive : (0 : Int) < denominator := by
    exact_mod_cast denominatorPositive
  rw [abs_le] at numeratorBound residual ⊢
  constructor <;> nlinarith

/-- A rational value within one guarded bit of the unit interval is safely
representable after nearest-even quantization in signed Q2 fixed point. -/
theorem encode_nearest_fits_q2
    (fractionalBits : Nat) (fractionalBits_min : 2 ≤ fractionalBits)
    (value : Rat)
    (bounded : |(value : ℝ)| ≤
      1 + 1 / (2 : ℝ) ^ (fractionalBits + 1)) :
    Fits ⟨fractionalBits + 2, fractionalBits⟩
      (encode .nearestTiesToEven
        ⟨fractionalBits + 2, fractionalBits⟩ value) := by
  let rawBoundNat : Nat := 2 * 2 ^ fractionalBits - 2
  let rawBound : Int := rawBoundNat
  unfold Fits
  apply FitsWidth.of_abs_le_signedMax
  · unfold encode
    apply abs_roundRatio_le .nearestTiesToEven _ _ rawBound value.den_pos
    · dsimp [rawBound]
      positivity
    · have scaleAtLeast : (4 : ℝ) ≤ (2 ^ fractionalBits : Nat) := by
        have natural : 2 ^ 2 ≤ 2 ^ fractionalBits :=
          Nat.pow_le_pow_right (by omega) fractionalBits_min
        norm_num at natural
        exact_mod_cast natural
      push_cast at scaleAtLeast
      have valueIdentity : (value : ℝ) = value.num / value.den := by
        rw [Rat.cast_def]
      have denominatorPositive : (0 : ℝ) < value.den := by
        exact_mod_cast value.den_pos
      have desiredReal :
          |(value.num : ℝ) * (2 ^ fractionalBits : Nat)| ≤
            ((rawBound : Int) : ℝ) * value.den := by
        rw [abs_mul, abs_of_nonneg (by positivity :
          (0 : ℝ) ≤ (2 ^ fractionalBits : Nat))]
        rw [valueIdentity, abs_div, abs_of_pos denominatorPositive] at bounded
        dsimp [rawBound, rawBoundNat]
        push_cast
        have scalePositive : (0 : ℝ) < (2 : ℝ) ^ fractionalBits := by
          positivity
        have denominatorNonnegative : (0 : ℝ) ≤ value.den :=
          denominatorPositive.le
        have powerSucc : (2 : ℝ) ^ (fractionalBits + 1) =
            2 * (2 : ℝ) ^ fractionalBits := by rw [pow_succ]; ring
        rw [powerSucc] at bounded
        have scaledBound :
            |(value.num : ℝ)| ≤
              (1 + 1 / (2 * (2 : ℝ) ^ fractionalBits)) * value.den :=
          (div_le_iff₀ denominatorPositive).mp bounded
        have coefficient :
            1 + 1 / (2 * (2 : ℝ) ^ fractionalBits) ≤
              2 - 2 / (2 : ℝ) ^ fractionalBits := by
          have denominator : (0 : ℝ) < 2 * (2 : ℝ) ^ fractionalBits := by
            positivity
          have combined :
              1 / (2 * (2 : ℝ) ^ fractionalBits) +
                  2 / (2 : ℝ) ^ fractionalBits =
                5 / (2 * (2 : ℝ) ^ fractionalBits) := by
            field_simp
            ring
          have fractionLeOne :
              5 / (2 * (2 : ℝ) ^ fractionalBits) ≤ 1 := by
            apply (div_le_one denominator).2
            nlinarith [scaleAtLeast]
          linarith
        calc
          |(value.num : ℝ)| * (2 : ℝ) ^ fractionalBits ≤
              ((1 + 1 / (2 * (2 : ℝ) ^ fractionalBits)) * value.den) *
                (2 : ℝ) ^ fractionalBits :=
            mul_le_mul_of_nonneg_right scaledBound scalePositive.le
          _ ≤ ((2 - 2 / (2 : ℝ) ^ fractionalBits) * value.den) *
                (2 : ℝ) ^ fractionalBits := by
            gcongr
          _ = (2 * (2 : ℝ) ^ fractionalBits - 2) * value.den := by
            field_simp
          _ = ((rawBoundNat : Nat) : ℝ) * value.den := by
            have powerPositive : 0 < 2 ^ fractionalBits := pow_pos (by omega) _
            have enough : 2 ≤ 2 * 2 ^ fractionalBits := by omega
            dsimp [rawBoundNat]
            rw [Nat.cast_sub enough]
            push_cast
            rfl
      simpa [Format.scale] using (show
        |value.num * (2 ^ fractionalBits : Nat)| ≤
          rawBound * value.den from by exact_mod_cast desiredReal)
  · dsimp [rawBound, signedMax]
    have powerPositive : 0 < 2 ^ fractionalBits := pow_pos (by omega) _
    have enough : 2 ≤ 2 * 2 ^ fractionalBits := by omega
    dsimp [rawBoundNat]
    rw [Nat.cast_sub enough, pow_succ]
    push_cast
    omega

@[simp]
theorem rescale_eq_self_of_eq (mode : RoundingMode) (fractionalBits : Nat)
    (raw : Int) :
    rescale mode fractionalBits fractionalBits raw = raw := by
  simp [rescale]

end HTFFT.FixedPoint
