import HTFFT.Fixed.Twiddle8Accuracy

namespace HTFFTTests.Twiddle8Accuracy

open HTFFT
open HTFFT.Fixed
open HTFFT.FixedPoint
open HTFFT.Fixed.Twiddle8

example :
    boundsAt config twiddleError
        { magnitude := 1, error := 0 } (Fin.last 3) =
      { magnitude := 8
        error := 25 * Real.sqrt 2 / 256 + 9 / 32768 } :=
  decoded_bounds

example :
    boundsAt config twiddleError
        { magnitude := 1, error := Real.sqrt 2 / 256 } (Fin.last 3) =
      { magnitude := 8
        error := 33 * Real.sqrt 2 / 256 + 13 / 32768 } :=
  encoded_bounds

example (input : Vector 3)
    (inputMagnitude : MagnitudeBound 1 (decodeVector config 0 input)) :
    NoOverflow config table input :=
  noOverflow_of_input_magnitude input inputMagnitude

example (input : Vector 3)
    (inputMagnitude : MagnitudeBound 1 (decodeVector config 0 input))
    (index : Fin 8) :
    ‖decodeVector config (Fin.last 3) (layeredFFT config table input) index -
          ZMod.dft
            (Exact.toZModVector (decodeVector config 0 input))
            (Exact.zmodIndexEquiv 3 index)‖ ≤
      25 * Real.sqrt 2 / 256 + 9 / 32768 :=
  decoded_fft_pointwise_dft input inputMagnitude index

example (inputRounding : RoundingMode)
    (input : Fin 8 → HTFFT.Complex Rat)
    (inputMagnitude : MagnitudeBound 1
      (rationalInputToComplex (depth := 3) input))
    (index : Fin 8) :
    ‖decodeVector config (Fin.last 3)
            (layeredFFT config table (encodeInput config inputRounding input))
            index -
          ZMod.dft (Exact.toZModVector
              (rationalInputToComplex (depth := 3) input))
            (Exact.zmodIndexEquiv 3 index)‖ ≤
      33 * Real.sqrt 2 / 256 + 13 / 32768 :=
  encoded_fft_pointwise_dft inputRounding input inputMagnitude index

end HTFFTTests.Twiddle8Accuracy
