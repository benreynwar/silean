import HTFFT.Fixed.LayeredCorrectness
import HTFFT.Fixed.LayeredRange
import HTFFT.Fixed.Twiddle8

namespace HTFFT.Fixed.Twiddle8

open HTFFT
open HTFFT.FixedPoint

/-- The concrete eight-point configuration is the standard initial policy:
Q4.8 input components, one growth bit per layer, and Q2.8 twiddles. -/
theorem config_eq_initial : config = Config.initial 3 12 8 10 8 :=
  rfl

/-- Every generated Q2.8 twiddle component has magnitude at most one encoded
unit (`256` in raw integer form). -/
theorem table_component_bound (stage : Fin 3)
    (offset : Fin (2 ^ stage.val)) :
    ComplexBound 256 (table.value stage offset) := by
  fin_cases stage <;> fin_cases offset <;>
    norm_num [table, config, twiddleFormat, quantizeTwiddleTable, approximations,
      rounding, diagonal, FixedPoint.encodeComplex, HTFFT.Complex.map,
      FixedPoint.encode, FixedPoint.roundRatio, Format.scale, ComplexBound]

/-- The static widths of the eight-point configuration accommodate the
conservative raw recurrence `B ↦ 3B+1` from an initial bound of `256`. -/
theorem initial_range_safe : InitialRangeSafe 3 12 10 8 256 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · norm_num [signedMax]
  · intro stage
    fin_cases stage <;> norm_num [rawBoundAfter, signedMax]

/-- The same widths also accommodate the extra raw unit allowed when an exact
input of magnitude one is first quantized to Q4.8. -/
theorem encoded_range_safe : InitialRangeSafe 3 12 10 8 257 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · norm_num [signedMax]
  · intro stage
    fin_cases stage <;> norm_num [rawBoundAfter, signedMax]

/-- A decoded Euclidean input magnitude of at most one is sufficient for
all fixed-width boundaries of this eight-point FFT to avoid wrapping. -/
theorem noOverflow_of_input_magnitude (input : Vector 3)
    (inputMagnitude : MagnitudeBound 1 (decodeVector config 0 input)) :
    NoOverflow config table input := by
  have inputBounded : VectorBound 256 input := by
    apply vectorBound_of_decodedMagnitude config 0 input 256
    simpa [config, Format.scale] using inputMagnitude
  rw [config_eq_initial]
  exact noOverflow_initial_of_bound 3 12 8 10 8 table input 256
    inputBounded table_component_bound initial_range_safe

/-- Quantizing an exact input whose Euclidean magnitude is at most one
still leaves sufficient range at every layer. -/
theorem noOverflow_encodedInput (inputRounding : RoundingMode)
    (input : Fin 8 → HTFFT.Complex Rat)
    (inputMagnitude : MagnitudeBound 1
      (rationalInputToComplex (depth := 3) input)) :
    NoOverflow config table (encodeInput config inputRounding input) := by
  have encodedMagnitude : ComponentMagnitudeBound (257 / 256)
      (decodeVector config 0 (encodeInput config inputRounding input)) := by
    convert encodeInput_componentMagnitudeBound config inputRounding input 1
      inputMagnitude using 1
    all_goals norm_num [quantum, config]
  have inputBounded :
      VectorBound 257 (encodeInput config inputRounding input) := by
    apply vectorBound_of_decodedComponentMagnitude config 0 _ 257
    simpa [config, Format.scale] using encodedMagnitude
  rw [config_eq_initial]
  exact noOverflow_initial_of_bound 3 12 8 10 8 table
    (encodeInput (Config.initial 3 12 8 10 8) inputRounding input) 257
    inputBounded table_component_bound encoded_range_safe

/-- With decoded input magnitude at most one and zero initial error, the
Euclidean recurrence ends at magnitude `8` and error
`25 * sqrt 2 / 256 + 9 / 32768`. -/
theorem decoded_bounds :
    boundsAt config twiddleError
        { magnitude := 1, error := 0 } (Fin.last 3) =
      { magnitude := 8
        error := 25 * Real.sqrt 2 / 256 + 9 / 32768 } := by
  have stages : Exact.butterflyStagePrefix 3 (Fin.last 3) =
      [(0 : Fin 3), (1 : Fin 3), (2 : Fin 3)] := by decide
  rw [boundsAt, stages]
  norm_num [advanceBounds, arithmeticError, componentArithmeticError, quantum,
    config, Config.butterfly, twiddleError, componentApproximationError]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Including the Euclidean conversion of one Q4.8 component LSB gives the
explicit pre-quantization error bound
`33 * sqrt 2 / 256 + 13 / 32768`. -/
theorem encoded_bounds :
    boundsAt config twiddleError
        { magnitude := 1, error := Real.sqrt 2 / 256 } (Fin.last 3) =
      { magnitude := 8
        error := 33 * Real.sqrt 2 / 256 + 13 / 32768 } := by
  have stages : Exact.butterflyStagePrefix 3 (Fin.last 3) =
      [(0 : Fin 3), (1 : Fin 3), (2 : Fin 3)] := by decide
  rw [boundsAt, stages]
  norm_num [advanceBounds, arithmeticError, componentArithmeticError, quantum,
    config, Config.butterfly, twiddleError, componentApproximationError]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- End-to-end accuracy for input bit patterns. Inputs and outputs are Q4.8
and Q7.8 respectively. Error uses ordinary Euclidean complex magnitude.
Output index `k` is the natural-frequency DFT index `k`, with no final
permutation. -/
theorem decoded_fft_pointwise_dft (input : Vector 3)
    (inputMagnitude : MagnitudeBound 1 (decodeVector config 0 input))
    (index : Fin 8) :
    ‖decodeVector config (Fin.last 3) (layeredFFT config table input) index -
          ZMod.dft
            (Exact.toZModVector (decodeVector config 0 input))
            (Exact.zmodIndexEquiv 3 index)‖ ≤
      25 * Real.sqrt 2 / 256 + 9 / 32768 := by
  have bounded := layeredFFT_pointwise_dft config table twiddleError
    input (decodeVector config 0 input)
    { magnitude := 1, error := 0 } (by constructor <;> norm_num)
    accuracy inputMagnitude (by intro inputIndex; simp)
    (noOverflow_of_input_magnitude input inputMagnitude) index
  rw [decoded_bounds] at bounded
  exact bounded

/-- End-to-end Euclidean accuracy relative to an intended rational input
before Q4.8 quantization, in natural-frequency order. -/
theorem encoded_fft_pointwise_dft (inputRounding : RoundingMode)
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
      33 * Real.sqrt 2 / 256 + 13 / 32768 := by
  have inputWithin : Within (Real.sqrt 2 / 256)
      (decodeVector config 0 (encodeInput config inputRounding input))
      (rationalInputToComplex (depth := 3) input) := by
    convert encodeInput_within config inputRounding input using 1
    all_goals norm_num [quantum, config]
    all_goals ring
  have bounded := layeredFFT_pointwise_dft config table twiddleError
    (encodeInput config inputRounding input)
    (rationalInputToComplex (depth := 3) input)
    { magnitude := 1, error := Real.sqrt 2 / 256 }
    (by constructor <;> positivity) accuracy inputMagnitude inputWithin
    (noOverflow_encodedInput inputRounding input inputMagnitude) index
  rw [encoded_bounds] at bounded
  exact bounded

end HTFFT.Fixed.Twiddle8
