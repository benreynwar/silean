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

@[simp]
theorem rescale_eq_self_of_eq (mode : RoundingMode) (fractionalBits : Nat)
    (raw : Int) :
    rescale mode fractionalBits fractionalBits raw = raw := by
  simp [rescale]

end HTFFT.FixedPoint
