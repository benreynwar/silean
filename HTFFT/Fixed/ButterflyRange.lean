import HTFFT.Fixed.ButterflyCorrectness
import HTFFT.FixedPoint.Range

namespace HTFFT.Butterfly.Fixed

open HTFFT
open HTFFT.FixedPoint

@[simp]
theorem rescaleComplex_self (rounding : RoundingMode) (format : Format)
    (value : HTFFT.Complex Int) :
    rescaleComplex rounding format format value = value := by
  rcases value with ⟨real, imag⟩
  simp [rescaleComplex, HTFFT.Complex.map]

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
