import HTFFT.Fixed.Twiddle8

namespace HTFFTTests.TwiddleTable

open HTFFT
open HTFFT.Fixed
open HTFFT.Fixed.Twiddle8

#check RationalTwiddleTable
#check TwiddleEnclosure
#check quantizeTwiddleTable
#check twiddleAccuracy_of_enclosure
#check Twiddle8.accuracy

-- The rational centers are quantized into the expected Q2.8 integers.
#guard table.value (0 : Fin 3) (0 : Fin (2 ^ (0 : Fin 3).val)) ==
  ⟨256, 0⟩
#guard table.value (1 : Fin 3) (1 : Fin (2 ^ (1 : Fin 3).val)) ==
  ⟨0, -256⟩
#guard table.value (2 : Fin 3) (1 : Fin (2 ^ (2 : Fin 3).val)) ==
  ⟨181, -181⟩
#guard table.value (2 : Fin 3) (2 : Fin (2 ^ (2 : Fin 3).val)) ==
  ⟨0, -256⟩
#guard table.value (2 : Fin 3) (3 : Fin (2 ^ (2 : Fin 3).val)) ==
  ⟨-181, -181⟩

example : componentApproximationError (0 : Fin 3) = 0 := by
  rfl

example : componentApproximationError (1 : Fin 3) = 0 := by
  rfl

example : componentApproximationError (2 : Fin 3) = (1 / 256 : ℝ) := by
  rfl

example : twiddleError (2 : Fin 3) = Real.sqrt 2 / 256 := by
  rw [twiddleError]
  norm_num [componentApproximationError]
  ring

end HTFFTTests.TwiddleTable
