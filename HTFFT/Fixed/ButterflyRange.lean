import HTFFT.Fixed.ButterflyCorrectness
import HTFFT.FixedPoint.Range

namespace HTFFT.Fixed

open HTFFT
open HTFFT.FixedPoint

/-- The largest symmetric decoded component magnitude which is certainly
representable by a signed fixed-point format.  The negative endpoint has one
additional code; using the positive endpoint keeps absolute-value range
arguments symmetric. -/
noncomputable def decodedCapacity (format : Format) : ℝ :=
  (signedMax format.width : ℝ) / format.scale

/-- Convert a decoded componentwise magnitude bound back into the
corresponding raw-integer bound. -/
theorem complexBound_of_decode_le (format : Format)
    (value : HTFFT.Complex Int) (bound : Int)
    (decodedBound :
      componentNorm (decodeComplex format value) ≤
        (bound : ℝ) / format.scale) :
    ComplexBound bound value := by
  have scalePositive : (0 : ℝ) < format.scale := by
    simp [Format.scale]
  have realPart :
      (decodeComplex format value).re =
        (value.real : ℝ) / format.scale := by
    simp only [decodeComplex, FixedPoint.decodeComplex, HTFFT.Complex.map,
      FixedPoint.decode, rationalComplexToComplex_re]
    rw [Rat.cast_divInt]
    norm_cast
  have imagPart :
      (decodeComplex format value).im =
        (value.imag : ℝ) / format.scale := by
    simp only [decodeComplex, FixedPoint.decodeComplex, HTFFT.Complex.map,
      FixedPoint.decode, rationalComplexToComplex_im]
    rw [Rat.cast_divInt]
    norm_cast
  have realDecoded :=
    (abs_re_le_componentNorm (decodeComplex format value)).trans decodedBound
  have imagDecoded :=
    (abs_im_le_componentNorm (decodeComplex format value)).trans decodedBound
  rw [realPart, abs_div, abs_of_pos scalePositive] at realDecoded
  rw [imagPart, abs_div, abs_of_pos scalePositive] at imagDecoded
  have realRaw : |(value.real : ℝ)| ≤ bound := by
    apply (div_le_div_iff_of_pos_right scalePositive).mp
    simpa using realDecoded
  have imagRaw : |(value.imag : ℝ)| ≤ bound := by
    apply (div_le_div_iff_of_pos_right scalePositive).mp
    simpa using imagDecoded
  constructor
  · exact_mod_cast realRaw
  · exact_mod_cast imagRaw

/-- A decoded component bound by the symmetric capacity of its format gives
representability of the underlying scaled integer. -/
theorem complexFits_of_componentNorm_decode_le_capacity (format : Format)
    (value : HTFFT.Complex Int)
    (bounded : componentNorm (decodeComplex format value) ≤
      decodedCapacity format) :
    ComplexFits format value := by
  exact ComplexFits.of_bound
    (complexBound_of_decode_le format value (signedMax format.width)
      (by simpa [decodedCapacity] using bounded))
    (le_refl _)

end HTFFT.Fixed

namespace HTFFT.Butterfly.Fixed

open HTFFT
open HTFFT.FixedPoint

/-- The rounded complex multiplier can be range-checked without first
assuming that its result fits.  This is the local fact needed to derive, rather
than assume, the multiplier part of `NoOverflow`. -/
theorem multiplyRounded_componentNorm_le (config : Config)
    (data twiddle : HTFFT.Complex Int) (dataMagnitude twiddleMagnitude : ℝ)
    (dataBounded : ‖HTFFT.Fixed.decodeComplex config.dataFormat data‖ ≤
      dataMagnitude)
    (twiddleBounded :
      ‖HTFFT.Fixed.decodeComplex config.twiddleFormat twiddle‖ ≤
        twiddleMagnitude)
    (dataMagnitudeNonnegative : 0 ≤ dataMagnitude) :
    HTFFT.Fixed.componentNorm
        (HTFFT.Fixed.decodeComplex config.productFormat
          (multiplyRounded config data twiddle)) ≤
      dataMagnitude * twiddleMagnitude +
        HTFFT.Fixed.quantum config.productFormat := by
  let actualRat := FixedPoint.decodeComplex config.productFormat
    (multiplyRounded config data twiddle)
  let exactRat :=
    FixedPoint.decodeComplex config.dataFormat data *
      FixedPoint.decodeComplex config.twiddleFormat twiddle
  let actual := HTFFT.Fixed.decodeComplex config.productFormat
    (multiplyRounded config data twiddle)
  let exact := HTFFT.Fixed.decodeComplex config.dataFormat data *
    HTFFT.Fixed.decodeComplex config.twiddleFormat twiddle
  have close := multiplyRounded_within config data twiddle
  have realClose : |actual.re - exact.re| ≤
      HTFFT.Fixed.quantum config.productFormat := by
    have closeReal := close.1
    rw [rationalAbs_eq_abs] at closeReal
    have casted : |((actualRat.real - exactRat.real : Rat) : ℝ)| ≤
        ((config.productFormat.quantum : Rat) : ℝ) := by
      exact_mod_cast closeReal
    simpa [actual, exact, actualRat, exactRat,
      HTFFT.Fixed.decodeComplex, HTFFT.Fixed.rationalComplexToComplex,
      HTFFT.Complex.mul_real, HTFFT.Fixed.quantum_eq_cast] using casted
  have imagClose : |actual.im - exact.im| ≤
      HTFFT.Fixed.quantum config.productFormat := by
    have closeImag := close.2
    rw [rationalAbs_eq_abs] at closeImag
    have casted : |((actualRat.imag - exactRat.imag : Rat) : ℝ)| ≤
        ((config.productFormat.quantum : Rat) : ℝ) := by
      exact_mod_cast closeImag
    simpa [actual, exact, actualRat, exactRat,
      HTFFT.Fixed.decodeComplex, HTFFT.Fixed.rationalComplexToComplex,
      HTFFT.Complex.mul_imag, HTFFT.Fixed.quantum_eq_cast] using casted
  have exactMagnitude : ‖exact‖ ≤ dataMagnitude * twiddleMagnitude := by
    rw [show exact = HTFFT.Fixed.decodeComplex config.dataFormat data *
      HTFFT.Fixed.decodeComplex config.twiddleFormat twiddle by rfl, norm_mul]
    exact mul_le_mul dataBounded twiddleBounded
      (norm_nonneg _) dataMagnitudeNonnegative
  apply max_le
  · calc
      |actual.re| ≤ |actual.re - exact.re| + |exact.re| := by
        simpa only [sub_add_cancel] using
          (abs_add_le (actual.re - exact.re) exact.re)
      _ ≤ HTFFT.Fixed.quantum config.productFormat + ‖exact‖ :=
        add_le_add realClose (Complex.abs_re_le_norm exact)
      _ ≤ HTFFT.Fixed.quantum config.productFormat +
          dataMagnitude * twiddleMagnitude :=
        add_le_add (le_refl _) exactMagnitude
      _ = dataMagnitude * twiddleMagnitude +
          HTFFT.Fixed.quantum config.productFormat := by ring
  · calc
      |actual.im| ≤ |actual.im - exact.im| + |exact.im| := by
        simpa only [sub_add_cancel] using
          (abs_add_le (actual.im - exact.im) exact.im)
      _ ≤ HTFFT.Fixed.quantum config.productFormat + ‖exact‖ :=
        add_le_add imagClose (Complex.abs_im_le_norm exact)
      _ ≤ HTFFT.Fixed.quantum config.productFormat +
          dataMagnitude * twiddleMagnitude :=
        add_le_add (le_refl _) exactMagnitude
      _ = dataMagnitude * twiddleMagnitude +
          HTFFT.Fixed.quantum config.productFormat := by ring

@[simp]
theorem rescaleComplex_self (rounding : RoundingMode) (format : Format)
    (value : HTFFT.Complex Int) :
    rescaleComplex rounding format format value = value := by
  rcases value with ⟨real, imag⟩
  simp [rescaleComplex, HTFFT.Complex.map]

theorem rescaleComplex_eq_self_of_fractionalBits_eq
    (rounding : RoundingMode) (source destination : Format)
    (value : HTFFT.Complex Int)
    (sameFractionalBits :
      source.fractionalBits = destination.fractionalBits) :
    rescaleComplex rounding source destination value = value := by
  rcases value with ⟨real, imag⟩
  simp [rescaleComplex, HTFFT.Complex.map, sameFractionalBits]

/-- For the FFT's approved arithmetic policy, natural decoded magnitude
bounds and three format-capacity inequalities imply every local no-wrap fact.
The theorem talks about mathematical values; the raw-integer bookkeeping is
kept entirely inside this range layer. -/
theorem noOverflow_initial_of_magnitudes
    (dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits : Nat)
    (a b twiddle : HTFFT.Complex Int)
    (dataMagnitude twiddleMagnitude : ℝ)
    (dataMagnitudeNonnegative : 0 ≤ dataMagnitude)
    (aBounded :
      ‖HTFFT.Fixed.decodeComplex ⟨dataWidth, dataFractionalBits⟩ a‖ ≤
        dataMagnitude)
    (bBounded :
      ‖HTFFT.Fixed.decodeComplex ⟨dataWidth, dataFractionalBits⟩ b‖ ≤
        dataMagnitude)
    (twiddleBounded :
      ‖HTFFT.Fixed.decodeComplex ⟨twiddleWidth, twiddleFractionalBits⟩
        twiddle‖ ≤ twiddleMagnitude)
    (twiddleFits :
      ComplexFits ⟨twiddleWidth, twiddleFractionalBits⟩ twiddle)
    (dataFits : dataMagnitude ≤
      HTFFT.Fixed.decodedCapacity ⟨dataWidth, dataFractionalBits⟩)
    (productFits :
      dataMagnitude * twiddleMagnitude +
          HTFFT.Fixed.quantum ⟨dataWidth, dataFractionalBits⟩ ≤
        HTFFT.Fixed.decodedCapacity ⟨dataWidth, dataFractionalBits⟩)
    (outputFits :
      dataMagnitude +
            (dataMagnitude * twiddleMagnitude +
              HTFFT.Fixed.quantum ⟨dataWidth, dataFractionalBits⟩) ≤
        HTFFT.Fixed.decodedCapacity
          ⟨dataWidth + 1, dataFractionalBits⟩) :
    NoOverflow
      (Config.initial dataWidth dataFractionalBits twiddleWidth
        twiddleFractionalBits)
      a b twiddle := by
  let config := Config.initial dataWidth dataFractionalBits twiddleWidth
    twiddleFractionalBits
  let productMagnitude := dataMagnitude * twiddleMagnitude +
    HTFFT.Fixed.quantum ⟨dataWidth, dataFractionalBits⟩
  have aComponent :
      HTFFT.Fixed.componentNorm
          (HTFFT.Fixed.decodeComplex config.dataFormat a) ≤ dataMagnitude :=
    (HTFFT.Fixed.componentNorm_le_norm _).trans (by simpa [config, Config.initial] using aBounded)
  have bComponent :
      HTFFT.Fixed.componentNorm
          (HTFFT.Fixed.decodeComplex config.dataFormat b) ≤ dataMagnitude :=
    (HTFFT.Fixed.componentNorm_le_norm _).trans (by simpa [config, Config.initial] using bBounded)
  have aFits : ComplexFits config.dataFormat a :=
    HTFFT.Fixed.complexFits_of_componentNorm_decode_le_capacity _ _
      (aComponent.trans (by simpa [config, Config.initial] using dataFits))
  have bFits : ComplexFits config.dataFormat b :=
    HTFFT.Fixed.complexFits_of_componentNorm_decode_le_capacity _ _
      (bComponent.trans (by simpa [config, Config.initial] using dataFits))
  have alignedEq : alignedARounded config a = a := by
    simp [alignedARounded, config, Config.initial]
  have alignedFits :
      ComplexFits config.productFormat (alignedARounded config a) := by
    rw [alignedEq]
    exact aFits
  have productComponent :
      HTFFT.Fixed.componentNorm
          (HTFFT.Fixed.decodeComplex config.productFormat
            (multiplyRounded config b twiddle)) ≤ productMagnitude := by
    simpa [productMagnitude, config, Config.initial] using
      multiplyRounded_componentNorm_le config b twiddle dataMagnitude
        twiddleMagnitude bBounded twiddleBounded dataMagnitudeNonnegative
  have multipliedFits :
      ComplexFits config.productFormat (multiplyRounded config b twiddle) :=
    HTFFT.Fixed.complexFits_of_componentNorm_decode_le_capacity _ _
      (productComponent.trans (by
        simpa [productMagnitude, config, Config.initial] using productFits))
  have alignedWrapped : alignedA config a = a := by
    rw [alignedA, wrapComplex_eq_of_fits alignedFits, alignedEq]
  have multipliedWrapped :
      multiply config b twiddle = multiplyRounded config b twiddle := by
    rw [multiply, wrapComplex_eq_of_fits multipliedFits]
  have upperComponent :
      HTFFT.Fixed.componentNorm
          (HTFFT.Fixed.decodeComplex config.outputFormat
            (outputRounded config a b twiddle).upper) ≤
        dataMagnitude + productMagnitude := by
    have upperRaw : (outputRounded config a b twiddle).upper =
        a + multiplyRounded config b twiddle := by
      rw [outputRounded_upper, alignedWrapped, multipliedWrapped]
      exact rescaleComplex_eq_self_of_fractionalBits_eq _ _ _ _ (by rfl)
    rw [upperRaw]
    have decodedAdd :
        HTFFT.Fixed.decodeComplex config.outputFormat
            (a + multiplyRounded config b twiddle) =
          HTFFT.Fixed.decodeComplex config.dataFormat a +
            HTFFT.Fixed.decodeComplex config.productFormat
              (multiplyRounded config b twiddle) := by
      rw [HTFFT.Fixed.decodeComplex, FixedPoint.decodeComplex_add,
        HTFFT.Fixed.rationalComplexToComplex_add]
      rfl
    rw [decodedAdd]
    exact (HTFFT.Fixed.componentNorm_add_le _ _).trans
      (add_le_add aComponent productComponent)
  have lowerComponent :
      HTFFT.Fixed.componentNorm
          (HTFFT.Fixed.decodeComplex config.outputFormat
            (outputRounded config a b twiddle).lower) ≤
        dataMagnitude + productMagnitude := by
    have lowerRaw : (outputRounded config a b twiddle).lower =
        a - multiplyRounded config b twiddle := by
      rw [outputRounded_lower, alignedWrapped, multipliedWrapped]
      exact rescaleComplex_eq_self_of_fractionalBits_eq _ _ _ _ (by rfl)
    rw [lowerRaw]
    have decodedSub :
        HTFFT.Fixed.decodeComplex config.outputFormat
            (a - multiplyRounded config b twiddle) =
          HTFFT.Fixed.decodeComplex config.dataFormat a -
            HTFFT.Fixed.decodeComplex config.productFormat
              (multiplyRounded config b twiddle) := by
      rw [HTFFT.Fixed.decodeComplex, FixedPoint.decodeComplex_sub,
        HTFFT.Fixed.rationalComplexToComplex_sub]
      rfl
    rw [decodedSub]
    exact (HTFFT.Fixed.componentNorm_sub_le _ _).trans
      (add_le_add aComponent productComponent)
  have upperFits :
      ComplexFits config.outputFormat
        (outputRounded config a b twiddle).upper :=
    HTFFT.Fixed.complexFits_of_componentNorm_decode_le_capacity _ _
      (upperComponent.trans (by
        simpa [productMagnitude, config, Config.initial] using outputFits))
  have lowerFits :
      ComplexFits config.outputFormat
        (outputRounded config a b twiddle).lower :=
    HTFFT.Fixed.complexFits_of_componentNorm_decode_le_capacity _ _
      (lowerComponent.trans (by
        simpa [productMagnitude, config, Config.initial] using outputFits))
  exact ⟨aFits, bFits, by simpa [config, Config.initial] using twiddleFits,
    alignedFits, multipliedFits, upperFits, lowerFits⟩

/-- With the initial butterfly format policy, a bounded data value multiplied
by a twiddle whose raw components are at most one encoded unit has raw
component magnitude at most `2 * dataBound + 1`. The final unit is a
conservative allowance for any supported rounding mode. -/
theorem multiplyRounded_bound_initial (dataWidth dataFractionalBits
    twiddleWidth twiddleFractionalBits : Nat)
    (dataBound : Int) (data twiddle : HTFFT.Complex Int)
    (twiddleFractionalBitsPositive : 0 < twiddleFractionalBits)
    (dataBoundNonnegative : 0 ≤ dataBound)
    (dataBounded : ComplexBound dataBound data)
    (twiddleBounded :
      ComplexBound (2 ^ twiddleFractionalBits : Nat) twiddle) :
    ComplexBound (2 * dataBound + 1)
      (multiplyRounded
        (Config.initial dataWidth dataFractionalBits twiddleWidth
          twiddleFractionalBits) data twiddle) := by
  let twiddleScale : Int := (2 ^ twiddleFractionalBits : Nat)
  have twiddleScalePositive : 0 < twiddleScale := by
    simp [twiddleScale]
  have realReal :
      |data.real * twiddle.real| ≤ dataBound * twiddleScale := by
    rw [abs_mul]
    exact mul_le_mul dataBounded.1 twiddleBounded.1
      (abs_nonneg _) dataBoundNonnegative
  have imagImag :
      |data.imag * twiddle.imag| ≤ dataBound * twiddleScale := by
    rw [abs_mul]
    exact mul_le_mul dataBounded.2 twiddleBounded.2
      (abs_nonneg _) dataBoundNonnegative
  have realImag :
      |data.real * twiddle.imag| ≤ dataBound * twiddleScale := by
    rw [abs_mul]
    exact mul_le_mul dataBounded.1 twiddleBounded.2
      (abs_nonneg _) dataBoundNonnegative
  have imagReal :
      |data.imag * twiddle.real| ≤ dataBound * twiddleScale := by
    rw [abs_mul]
    exact mul_le_mul dataBounded.2 twiddleBounded.1
      (abs_nonneg _) dataBoundNonnegative
  have realNumerator :
      |data.real * twiddle.real - data.imag * twiddle.imag| ≤
        (2 * dataBound) * twiddleScale := by
    calc
      |data.real * twiddle.real - data.imag * twiddle.imag| ≤
          |data.real * twiddle.real| + |data.imag * twiddle.imag| :=
        abs_sub _ _
      _ ≤ dataBound * twiddleScale + dataBound * twiddleScale :=
        add_le_add realReal imagImag
      _ = (2 * dataBound) * twiddleScale := by ring
  have imagNumerator :
      |data.real * twiddle.imag + data.imag * twiddle.real| ≤
        (2 * dataBound) * twiddleScale := by
    calc
      |data.real * twiddle.imag + data.imag * twiddle.real| ≤
          |data.real * twiddle.imag| + |data.imag * twiddle.real| :=
        abs_add_le _ _
      _ ≤ dataBound * twiddleScale + dataBound * twiddleScale :=
        add_le_add realImag imagReal
      _ = (2 * dataBound) * twiddleScale := by ring
  have gapNotOrdered :
      ¬ (dataFractionalBits + twiddleFractionalBits ≤
        dataFractionalBits) := by omega
  constructor
  · change
      |rescale .nearestTiesToEven
          (dataFractionalBits + twiddleFractionalBits)
          dataFractionalBits
          (data.real * twiddle.real - data.imag * twiddle.imag)| ≤
        2 * dataBound + 1
    rw [rescale, if_neg gapNotOrdered]
    exact abs_roundRatio_le .nearestTiesToEven _ _ (2 * dataBound)
      (by positivity) (by omega) (by simpa [twiddleScale] using realNumerator)
  · change
      |rescale .nearestTiesToEven
          (dataFractionalBits + twiddleFractionalBits)
          dataFractionalBits
          (data.real * twiddle.imag + data.imag * twiddle.real)| ≤
        2 * dataBound + 1
    rw [rescale, if_neg gapNotOrdered]
    exact abs_roundRatio_le .nearestTiesToEven _ _ (2 * dataBound)
      (by positivity) (by omega) (by simpa [twiddleScale] using imagNumerator)

/-- A reusable range theorem for the approved initial butterfly policy. It
both discharges every internal no-wrap boundary and propagates the symmetric
raw component bound from `B` to `3 * B + 1`. -/
theorem butterfly_initial_noOverflow_and_bound
    (dataWidth dataFractionalBits twiddleWidth twiddleFractionalBits : Nat)
    (dataBound : Int) (a b twiddle : HTFFT.Complex Int)
    (twiddleFractionalBitsPositive : 0 < twiddleFractionalBits)
    (dataBoundNonnegative : 0 ≤ dataBound)
    (aBounded : ComplexBound dataBound a)
    (bBounded : ComplexBound dataBound b)
    (twiddleBounded :
      ComplexBound (2 ^ twiddleFractionalBits : Nat) twiddle)
    (twiddleFits :
      (2 ^ twiddleFractionalBits : Nat) ≤ signedMax twiddleWidth)
    (productFits : 2 * dataBound + 1 ≤ signedMax dataWidth)
    (outputFits : 3 * dataBound + 1 ≤ signedMax (dataWidth + 1)) :
    let config := Config.initial dataWidth dataFractionalBits twiddleWidth
      twiddleFractionalBits
    NoOverflow config a b twiddle ∧
      ComplexBound (3 * dataBound + 1)
        (butterfly config a b twiddle).upper ∧
      ComplexBound (3 * dataBound + 1)
        (butterfly config a b twiddle).lower := by
  let config := Config.initial dataWidth dataFractionalBits twiddleWidth
    twiddleFractionalBits
  have dataFits : dataBound ≤ signedMax dataWidth := by
    omega
  have aFits : ComplexFits config.dataFormat a :=
    ComplexFits.of_bound aBounded dataFits
  have bFits : ComplexFits config.dataFormat b :=
    ComplexFits.of_bound bBounded dataFits
  have storedTwiddleFits : ComplexFits config.twiddleFormat twiddle :=
    ComplexFits.of_bound twiddleBounded twiddleFits
  have alignedEq : alignedARounded config a = a := by
    simp [alignedARounded, config, Config.initial]
  have alignedFits :
      ComplexFits config.productFormat (alignedARounded config a) := by
    rw [alignedEq]
    exact aFits
  have productBounded :
      ComplexBound (2 * dataBound + 1)
        (multiplyRounded config b twiddle) := by
    exact multiplyRounded_bound_initial dataWidth dataFractionalBits
      twiddleWidth twiddleFractionalBits dataBound b twiddle
      twiddleFractionalBitsPositive dataBoundNonnegative bBounded
      twiddleBounded
  have multipliedFits :
      ComplexFits config.productFormat (multiplyRounded config b twiddle) :=
    ComplexFits.of_bound productBounded productFits
  have alignedWrapped : alignedA config a = a := by
    rw [alignedA, wrapComplex_eq_of_fits alignedFits, alignedEq]
  have multipliedWrapped :
      multiply config b twiddle = multiplyRounded config b twiddle := by
    rw [multiply, wrapComplex_eq_of_fits multipliedFits]
  have upperBounded :
      ComplexBound (3 * dataBound + 1)
        (outputRounded config a b twiddle).upper := by
    rw [outputRounded_upper, alignedWrapped, multipliedWrapped]
    simp only [config, Config.initial, rescaleComplex, HTFFT.Complex.map,
      rescale_eq_self_of_eq]
    constructor
    · calc
        |a.real + (multiplyRounded config b twiddle).real| ≤
            |a.real| + |(multiplyRounded config b twiddle).real| :=
          abs_add_le _ _
        _ ≤ dataBound + (2 * dataBound + 1) :=
          add_le_add aBounded.1 productBounded.1
        _ = 3 * dataBound + 1 := by ring
    · calc
        |a.imag + (multiplyRounded config b twiddle).imag| ≤
            |a.imag| + |(multiplyRounded config b twiddle).imag| :=
          abs_add_le _ _
        _ ≤ dataBound + (2 * dataBound + 1) :=
          add_le_add aBounded.2 productBounded.2
        _ = 3 * dataBound + 1 := by ring
  have lowerBounded :
      ComplexBound (3 * dataBound + 1)
        (outputRounded config a b twiddle).lower := by
    rw [outputRounded_lower, alignedWrapped, multipliedWrapped]
    simp only [config, Config.initial, rescaleComplex, HTFFT.Complex.map,
      rescale_eq_self_of_eq]
    constructor
    · calc
        |a.real - (multiplyRounded config b twiddle).real| ≤
            |a.real| + |(multiplyRounded config b twiddle).real| :=
          abs_sub _ _
        _ ≤ dataBound + (2 * dataBound + 1) :=
          add_le_add aBounded.1 productBounded.1
        _ = 3 * dataBound + 1 := by ring
    · calc
        |a.imag - (multiplyRounded config b twiddle).imag| ≤
            |a.imag| + |(multiplyRounded config b twiddle).imag| :=
          abs_sub _ _
        _ ≤ dataBound + (2 * dataBound + 1) :=
          add_le_add aBounded.2 productBounded.2
        _ = 3 * dataBound + 1 := by ring
  have upperFits :
      ComplexFits config.outputFormat
        (outputRounded config a b twiddle).upper :=
    ComplexFits.of_bound upperBounded outputFits
  have lowerFits :
      ComplexFits config.outputFormat
        (outputRounded config a b twiddle).lower :=
    ComplexFits.of_bound lowerBounded outputFits
  have noOverflow : NoOverflow config a b twiddle :=
    ⟨aFits, bFits, storedTwiddleFits, alignedFits, multipliedFits,
      upperFits, lowerFits⟩
  refine ⟨noOverflow, ?_, ?_⟩
  · rw [butterfly_eq_outputRounded_of_noOverflow noOverflow]
    exact upperBounded
  · rw [butterfly_eq_outputRounded_of_noOverflow noOverflow]
    exact lowerBounded

end HTFFT.Butterfly.Fixed
