import HTFFT.Fixed.LayeredCorrectness
import HTFFT.Silean.UnrolledFFT.UnrolledFFT

/-! Representation and numerical bridges for the unrolled FFT contract. -/

namespace HTFFT.Silean.UnrolledFFT

open _root_.Silean

/-- Decode a packed hardware output all the way into Mathlib complex values. -/
noncomputable def decodeOutput (configuration : Configuration depth)
    (output : Fin (2 ^ depth) →
      (UnrolledFFTLayer.complexSignalType
        (configuration.boundaryFormat (Fin.last depth))).Denote) :
    Fin (2 ^ depth) → ℂ :=
  HTFFT.Fixed.decodeVector configuration.fixedConfig (Fin.last depth)
    (UnrolledFFTLayer.decodeVector
      (configuration.boundaryFormat (Fin.last depth)) output)

/-- The natural fixed-point result is already represented canonically at the
hardware output width. -/
theorem resultValue_canonical
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (input : Fin (2 ^ depth) →
      (UnrolledFFTLayer.complexSignalType
        (configuration.boundaryFormat 0)).Denote) :
    (fun index => HTFFT.Butterfly.Fixed.wrapComplex
      (configuration.boundaryFormat (Fin.last depth))
      (resultValue configuration table input index)) =
      resultValue configuration table input := by
  have inputCanonical :
      (fun index => HTFFT.Butterfly.Fixed.wrapComplex
        (configuration.boundaryFormat 0)
        (UnrolledFFTLayer.decodeVector
          (configuration.boundaryFormat 0) input index)) =
        UnrolledFFTLayer.decodeVector
          (configuration.boundaryFormat 0) input := by
    funext index
    simp [UnrolledFFTLayer.decodeVector]
  simpa only [resultValue, FFTConfiguration.fixedConfig_boundaryFormat] using
    HTFFT.Fixed.wrapComplex_layeredFFT_of_canonical
      configuration.fixedConfig table
      (UnrolledFFTLayer.decodeVector
        (configuration.boundaryFormat 0) input)
      inputCanonical

/-- Encoding the contract result and decoding the hardware word loses no
information.  This bridge is unconditional; no-overflow is needed for the
subsequent numerical approximation theorem, not for packed representation. -/
@[simp] theorem decodeOutput_encode_resultValue
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (input : Fin (2 ^ depth) →
      (UnrolledFFTLayer.complexSignalType
        (configuration.boundaryFormat 0)).Denote) :
    decodeOutput configuration
        (UnrolledFFTLayer.encodeVector
          (configuration.boundaryFormat (Fin.last depth))
          (resultValue configuration table input)) =
      HTFFT.Fixed.decodeVector configuration.fixedConfig (Fin.last depth)
        (resultValue configuration table input) := by
  unfold decodeOutput
  rw [UnrolledFFTLayer.decodeVector_encodeVector,
    resultValue_canonical]

/-- One correct packed hardware result inherits the existing pure fixed-point
network error bound under exactly the pure model's no-overflow hypothesis. -/
theorem output_within
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (twiddleError : Fin depth → ℝ)
    (input : Fin (2 ^ depth) →
      (UnrolledFFTLayer.complexSignalType
        (configuration.boundaryFormat 0)).Denote)
    (output : Fin (2 ^ depth) →
      (UnrolledFFTLayer.complexSignalType
        (configuration.boundaryFormat (Fin.last depth))).Denote)
    (exactInput : HTFFT.Exact.Vector depth ℂ)
    (initial : HTFFT.Fixed.Bounds)
    (outputCorrect : output =
      UnrolledFFTLayer.encodeVector
        (configuration.boundaryFormat (Fin.last depth))
        (resultValue configuration table input))
    (initialNonnegative : initial.Nonnegative)
    (twiddleAccuracy : HTFFT.Fixed.TwiddleAccuracy
      configuration.fixedConfig table twiddleError)
    (inputMagnitude : HTFFT.Fixed.MagnitudeBound initial.magnitude exactInput)
    (inputWithin : HTFFT.Fixed.Within initial.error
      (HTFFT.Fixed.decodeVector configuration.fixedConfig 0
        (UnrolledFFTLayer.decodeVector
          (configuration.boundaryFormat 0) input))
      exactInput)
    (noOverflow : HTFFT.Fixed.NoOverflow configuration.fixedConfig table
      (UnrolledFFTLayer.decodeVector
        (configuration.boundaryFormat 0) input)) :
    HTFFT.Fixed.Within
      (HTFFT.Fixed.boundsAt configuration.fixedConfig twiddleError initial
        (Fin.last depth)).error
      (decodeOutput configuration output)
      (HTFFT.Exact.layeredFFT depth exactInput) := by
  subst output
  rw [decodeOutput_encode_resultValue]
  exact HTFFT.Fixed.layeredFFT_within configuration.fixedConfig table
    twiddleError
    (UnrolledFFTLayer.decodeVector
      (configuration.boundaryFormat 0) input)
    exactInput initial initialNonnegative twiddleAccuracy inputMagnitude
    inputWithin noOverflow

/-- Pointwise DFT form of `output_within`.  This is the direct numerical
bridge from one relation instance of the hardware contract to Mathlib's DFT. -/
theorem output_pointwise_dft
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (twiddleError : Fin depth → ℝ)
    (input : Fin (2 ^ depth) →
      (UnrolledFFTLayer.complexSignalType
        (configuration.boundaryFormat 0)).Denote)
    (output : Fin (2 ^ depth) →
      (UnrolledFFTLayer.complexSignalType
        (configuration.boundaryFormat (Fin.last depth))).Denote)
    (exactInput : HTFFT.Exact.Vector depth ℂ)
    (initial : HTFFT.Fixed.Bounds)
    (outputCorrect : output =
      UnrolledFFTLayer.encodeVector
        (configuration.boundaryFormat (Fin.last depth))
        (resultValue configuration table input))
    (initialNonnegative : initial.Nonnegative)
    (twiddleAccuracy : HTFFT.Fixed.TwiddleAccuracy
      configuration.fixedConfig table twiddleError)
    (inputMagnitude : HTFFT.Fixed.MagnitudeBound initial.magnitude exactInput)
    (inputWithin : HTFFT.Fixed.Within initial.error
      (HTFFT.Fixed.decodeVector configuration.fixedConfig 0
        (UnrolledFFTLayer.decodeVector
          (configuration.boundaryFormat 0) input))
      exactInput)
    (noOverflow : HTFFT.Fixed.NoOverflow configuration.fixedConfig table
      (UnrolledFFTLayer.decodeVector
        (configuration.boundaryFormat 0) input))
    (index : Fin (2 ^ depth)) :
    ‖decodeOutput configuration output index -
        ZMod.dft (HTFFT.Exact.toZModVector exactInput)
          (HTFFT.Exact.zmodIndexEquiv depth index)‖ ≤
      (HTFFT.Fixed.boundsAt configuration.fixedConfig twiddleError initial
        (Fin.last depth)).error := by
  have bounded := output_within configuration table twiddleError input output
    exactInput initial outputCorrect initialNonnegative twiddleAccuracy
    inputMagnitude inputWithin noOverflow index
  rw [HTFFT.Exact.layeredFFT_agreesWithDFT] at bounded
  exact bounded

end HTFFT.Silean.UnrolledFFT
