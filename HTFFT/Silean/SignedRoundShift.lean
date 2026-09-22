import HTFFT.FixedPoint
import Silean.Modules.SignedRoundShift.SignedRoundShift

/-! The semantic bridge between Silean's signed rounded shift and HTFFT's
pure fixed-point rescaling operation. -/

namespace HTFFT.Silean.SignedRoundShift

open HTFFT.FixedPoint

abbrev roundNearestEven :=
  _root_.Silean.Modules.SignedRoundShift.roundNearestEven

abbrev resultValue :=
  _root_.Silean.Modules.SignedRoundShift.resultValue

/-- Silean's nearest-even integer operation is exactly the corresponding
power-of-two instance of the pure fixed-point rounding specification. -/
theorem roundNearestEven_eq_roundRatio (discardedWidth : Nat) (value : Int) :
    roundNearestEven discardedWidth value =
      roundRatio .nearestTiesToEven value (2 ^ discardedWidth) := by
  simp [roundNearestEven,
    _root_.Silean.Modules.SignedRoundShift.roundNearestEven,
    roundRatio]

/-- The Silean contract returns exactly HTFFT's destination-width signed
encoding of the rounded integer. -/
theorem resultValue_eq_encodeSigned (retainedWidth discardedWidth : Nat)
    (value : Fin (discardedWidth + retainedWidth) → Bool) :
    _root_.Silean.BitVector.toBitVec retainedWidth
        (resultValue retainedWidth discardedWidth value) =
      encodeSigned retainedWidth
        (roundRatio .nearestTiesToEven
          (_root_.Silean.BitVector.toBitVec
            (discardedWidth + retainedWidth) value).toInt
          (2 ^ discardedWidth)) := by
  simp [resultValue,
    _root_.Silean.Modules.SignedRoundShift.resultValue,
    encodeSigned, roundNearestEven_eq_roundRatio]

/-- Interpreting the contract result as two's complement gives the explicitly
wrapped pure fixed-point rounded value. -/
theorem interpret_resultValue (retainedWidth discardedWidth : Nat)
    (value : Fin (discardedWidth + retainedWidth) → Bool) :
    interpretSigned
        (_root_.Silean.BitVector.toBitVec retainedWidth
          (resultValue retainedWidth discardedWidth value)) =
      wrapSigned retainedWidth
        (roundRatio .nearestTiesToEven
          (_root_.Silean.BitVector.toBitVec
            (discardedWidth + retainedWidth) value).toInt
          (2 ^ discardedWidth)) := by
  rw [resultValue_eq_encodeSigned, interpretSigned_encodeSigned]

end HTFFT.Silean.SignedRoundShift
