import HTFFT.Silean.PipelinedSignedComplexMultiply.PipelinedSignedComplexMultiply
import Silean.Modules.VectorLayout.VectorLayout

/-! Width normalization and the wire-only adapter used before rounded shifts. -/

namespace HTFFT.Silean.PipelinedSignedComplexMultiply.Internal

open _root_.Silean
open _root_.Silean.Modules

/-- The rounder never needs to inspect more bits than the numerator contains. -/
def effectiveDiscard (leftWidth rightWidth discardedWidth : Nat) : Nat :=
  min discardedWidth (numeratorWidth leftWidth rightWidth)

def roundInputWidth (leftWidth rightWidth discardedWidth : Nat) : Nat :=
  effectiveDiscard leftWidth rightWidth discardedWidth +
    resultWidth leftWidth rightWidth discardedWidth

theorem numeratorWidth_eq (leftWidth rightWidth : Nat) :
    numeratorWidth leftWidth rightWidth =
      productWidth leftWidth rightWidth + 1 := by
  simp [numeratorWidth, Arithmetic.resultWidth]

theorem roundInputWidth_eq_numeratorWidth
    (leftWidth rightWidth discardedWidth : Nat) :
    roundInputWidth leftWidth rightWidth discardedWidth =
      numeratorWidth leftWidth rightWidth := by
  simp only [roundInputWidth, effectiveDiscard, resultWidth]
  omega

/-- Re-express the exact numerator at the syntactic width expected by
`SignedRoundShift`.  The widths are propositionally equal, so every output bit
selects the same-index input bit and no logic is introduced. -/
def roundInputLayout (leftWidth rightWidth discardedWidth : Nat) :
    Fin (roundInputWidth leftWidth rightWidth discardedWidth) →
      VectorLayout.BitSource (numeratorWidth leftWidth rightWidth) :=
  fun index => .input ⟨index.val, by
    rw [← roundInputWidth_eq_numeratorWidth
      leftWidth rightWidth discardedWidth]
    exact index.isLt⟩

@[simp] theorem apply_roundInputLayout
    (leftWidth rightWidth discardedWidth : Nat)
    (input : Fin (numeratorWidth leftWidth rightWidth) → Bool)
    (index : Fin (roundInputWidth leftWidth rightWidth discardedWidth)) :
    VectorLayout.apply
        (roundInputLayout leftWidth rightWidth discardedWidth) input index =
      input ⟨index.val, by
        rw [← roundInputWidth_eq_numeratorWidth
          leftWidth rightWidth discardedWidth]
        exact index.isLt⟩ := by
  rfl

/-- The wire-only shape normalization preserves the signed packed value. -/
private theorem toInt_reindex_eq {leftWidth rightWidth : Nat}
    (widths : leftWidth = rightWidth)
    (left : Fin leftWidth → Bool) (right : Fin rightWidth → Bool)
    (bits : ∀ index, left index = right (Fin.cast widths index)) :
    (BitVector.toBitVec leftWidth left).toInt =
      (BitVector.toBitVec rightWidth right).toInt := by
  subst rightWidth
  have values : left = right := by
    funext index
    simpa using bits index
  subst right
  rfl

theorem toInt_apply_roundInputLayout
    (leftWidth rightWidth discardedWidth : Nat)
    (input : Fin (numeratorWidth leftWidth rightWidth) → Bool) :
    (BitVector.toBitVec
      (effectiveDiscard leftWidth rightWidth discardedWidth +
        resultWidth leftWidth rightWidth discardedWidth)
      (VectorLayout.apply
        (roundInputLayout leftWidth rightWidth discardedWidth) input)).toInt =
      (BitVector.toBitVec
        (numeratorWidth leftWidth rightWidth) input).toInt := by
  apply toInt_reindex_eq
    (roundInputWidth_eq_numeratorWidth
      leftWidth rightWidth discardedWidth)
  intro index
  rfl

/-- Saturating the inspected low-bit count changes no observable output.  In
the excessive-discard case the public result width is zero; otherwise the
effective and requested counts coincide. -/
theorem encode_roundNearestEven_effectiveDiscard
    (leftWidth rightWidth discardedWidth : Nat) (value : Int) :
    Arithmetic.encode (resultWidth leftWidth rightWidth discardedWidth)
        (SignedRoundShift.roundNearestEven
          (effectiveDiscard leftWidth rightWidth discardedWidth) value) =
      roundedValue leftWidth rightWidth discardedWidth value := by
  by_cases within : discardedWidth ≤ numeratorWidth leftWidth rightWidth
  · simp [effectiveDiscard, Nat.min_eq_left within, roundedValue]
  · have empty : resultWidth leftWidth rightWidth discardedWidth = 0 := by
      simp only [resultWidth]
      omega
    funext index
    have impossible := index.isLt
    omega

end HTFFT.Silean.PipelinedSignedComplexMultiply.Internal
