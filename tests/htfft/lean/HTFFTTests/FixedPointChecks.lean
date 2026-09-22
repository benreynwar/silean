import HTFFT.FixedPoint.Correctness

namespace HTFFTTests.FixedPoint

open HTFFT
open HTFFT.FixedPoint

def qTwo : Format := ⟨4, 2⟩

#guard qTwo.scale == 4
#guard signedMin 4 == -8
#guard signedMax 4 == 7

example : Fits qTwo (-8) := by
  simp [Fits, FitsWidth, qTwo, signedMin, signedMax]

example : Fits qTwo 7 := by
  simp [Fits, FitsWidth, qTwo, signedMin, signedMax]

example : ¬ Fits qTwo (-9) := by
  simp [Fits, FitsWidth, qTwo, signedMin, signedMax]

example : ¬ Fits qTwo 8 := by
  simp [Fits, FitsWidth, qTwo, signedMin, signedMax]

-- The binary point is an explicit part of the format, not inferred from width.
#guard decode qTwo 4 == Rat.divInt 1 1
#guard decode ⟨5, 2⟩ 4 == Rat.divInt 1 1

-- The three policies differ on negative and halfway values as intended.
#guard roundRatio .towardNegative (-3) 2 == -2
#guard roundRatio .towardZero (-3) 2 == -1
#guard roundRatio .nearestTiesToEven 5 2 == 2
#guard roundRatio .nearestTiesToEven 7 2 == 4
#guard roundRatio .nearestTiesToEven (-5) 2 == -2
#guard roundRatio .nearestTiesToEven (-7) 2 == -4

#guard rescale .nearestTiesToEven 2 4 3 == 12
#guard rescale .nearestTiesToEven 4 2 10 == 2

-- Overflow is a separate, visible operation.
#guard wrapSigned 4 8 == -8
#guard wrapSigned 4 (-9) == 7

#guard interpretSigned (encodeSigned 4 8) == -8
#guard encodeSigned 4 (interpretSigned (0b1011 : BitVec 4)) ==
  (0b1011 : BitVec 4)

-- Quantization is exact when the rational lies on the destination grid.
#guard encode .nearestTiesToEven qTwo (Rat.divInt 3 4) == 3

example :
    decode ⟨6, 4⟩ (rescale .nearestTiesToEven 2 4 3) = decode qTwo 3 := by
  exact decode_rescale_of_le .nearestTiesToEven qTwo ⟨6, 4⟩ 3 (by
    simp [qTwo])

example :
    |decode qTwo (encode .nearestTiesToEven qTwo (Rat.divInt 5 8)) -
      Rat.divInt 5 8| ≤ qTwo.quantum := by
  exact decode_encode_error _ _ _

example : wrapSigned 4 7 = 7 := by
  apply wrapSigned_eq_of_fits
  simp [FitsWidth, signedMin, signedMax]

end HTFFTTests.FixedPoint
