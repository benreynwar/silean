import HTFFT.Butterfly
import HTFFT.FixedPoint.Correctness
import HTFFT.Silean.SignedRoundShift
import HTFFT.Silean.PipelinedSignedComplexMultiply.PipelinedSignedComplexMultiplyDerived

/-! Connect the structural complex multiplier's integer behavior to the pure
HTFFT fixed-point complex-multiplication specification. -/

namespace HTFFT.Silean.PipelinedSignedComplexMultiply

open HTFFT.FixedPoint

/-- Decode two component wires as an ordinary complex integer value. -/
def complexValue (width : Nat) (real imag : Fin width → Bool) :
    HTFFT.Complex Int :=
  { real := (_root_.Silean.BitVector.toBitVec width real).toInt
    imag := (_root_.Silean.BitVector.toBitVec width imag).toInt }

private theorem rescale_nearest_eq_roundNearestEven
    (destinationFractionalBits discardedWidth : Nat) (raw : Int) :
    rescale .nearestTiesToEven
        (destinationFractionalBits + discardedWidth)
        destinationFractionalBits raw =
      _root_.Silean.Modules.SignedRoundShift.roundNearestEven
        discardedWidth raw := by
  cases discardedWidth with
  | zero =>
      simp [rescale,
        HTFFT.Silean.SignedRoundShift.roundNearestEven_eq_roundRatio,
        roundRatio]
  | succ discardedWidth =>
      rw [rescale, if_neg (by omega)]
      have difference :
          destinationFractionalBits + (discardedWidth + 1) -
              destinationFractionalBits =
            discardedWidth + 1 := by omega
      rw [difference]
      exact
        (HTFFT.Silean.SignedRoundShift.roundNearestEven_eq_roundRatio
          (discardedWidth + 1) raw).symm

private theorem interpret_roundedValue_of_fits
    (leftWidth rightWidth discardedWidth : Nat) (raw : Int)
    (fits : FitsWidth
      (resultWidth leftWidth rightWidth discardedWidth)
      (_root_.Silean.Modules.SignedRoundShift.roundNearestEven
        discardedWidth raw)) :
    interpretSigned
        (_root_.Silean.BitVector.toBitVec
          (resultWidth leftWidth rightWidth discardedWidth)
          (_root_.HTFFT.Silean.PipelinedSignedComplexMultiply.roundedValue
            leftWidth rightWidth discardedWidth raw)) =
      _root_.Silean.Modules.SignedRoundShift.roundNearestEven
        discardedWidth raw := by
  simp only [
    _root_.HTFFT.Silean.PipelinedSignedComplexMultiply.roundedValue,
    _root_.Silean.Modules.Arithmetic.encode,
    _root_.Silean.BitVector.toBitVec_ofBitVec]
  change interpretSigned
      (encodeSigned
        (resultWidth leftWidth rightWidth discardedWidth)
        (_root_.Silean.Modules.SignedRoundShift.roundNearestEven
          discardedWidth raw)) = _
  rw [interpretSigned_encodeSigned, wrapSigned_eq_of_fits fits]

/-- The contract values are the fixed-width encodings of the pure rounded
complex product.  Unlike the decoded-value bridge below, this bit-level fact
does not require representability: wrapping remains visible in the encoding
and can be composed with a later explicit width boundary. -/
theorem resultValues_eq_encode_multiplyRounded
    (config : HTFFT.Butterfly.Fixed.Config)
    (leftWidth rightWidth discardedWidth : Nat)
    (leftReal leftImag : Fin leftWidth → Bool)
    (rightReal rightImag : Fin rightWidth → Bool)
    (rounding : config.rounding = .nearestTiesToEven)
    (fractionalBits :
      config.dataFormat.fractionalBits +
          config.twiddleFormat.fractionalBits =
        config.productFormat.fractionalBits + discardedWidth) :
    realResultValue leftWidth rightWidth discardedWidth
        leftReal leftImag rightReal rightImag =
        _root_.Silean.Modules.Arithmetic.encode
          (resultWidth leftWidth rightWidth discardedWidth)
          (HTFFT.Butterfly.Fixed.multiplyRounded config
            (complexValue leftWidth leftReal leftImag)
            (complexValue rightWidth rightReal rightImag)).real ∧
      imagResultValue leftWidth rightWidth discardedWidth
        leftReal leftImag rightReal rightImag =
        _root_.Silean.Modules.Arithmetic.encode
          (resultWidth leftWidth rightWidth discardedWidth)
          (HTFFT.Butterfly.Fixed.multiplyRounded config
            (complexValue leftWidth leftReal leftImag)
            (complexValue rightWidth rightReal rightImag)).imag := by
  have finish (raw : Int) :
      _root_.Silean.Modules.SignedRoundShift.roundNearestEven
          discardedWidth raw =
        rescale config.rounding
          (config.dataFormat.fractionalBits +
            config.twiddleFormat.fractionalBits)
          config.productFormat.fractionalBits raw := by
    rw [rounding, fractionalBits]
    exact (rescale_nearest_eq_roundNearestEven
      config.productFormat.fractionalBits discardedWidth raw).symm
  constructor
  · unfold realResultValue roundedValue
    simp only [HTFFT.Butterfly.Fixed.multiplyRounded, complexValue]
    rw [← finish]
    rfl
  · unfold imagResultValue roundedValue
    simp only [HTFFT.Butterfly.Fixed.multiplyRounded, complexValue]
    rw [← finish]
    rfl

/-- Subject only to the chosen binary-point relation and representability of
the unwrapped result, the two Silean contract values decode to exactly
`Butterfly.Fixed.multiplyRounded`. -/
theorem resultValues_eq_multiplyRounded
    (config : HTFFT.Butterfly.Fixed.Config)
    (leftWidth rightWidth discardedWidth : Nat)
    (leftReal leftImag : Fin leftWidth → Bool)
    (rightReal rightImag : Fin rightWidth → Bool)
    (rounding : config.rounding = .nearestTiesToEven)
    (fractionalBits :
      config.dataFormat.fractionalBits +
          config.twiddleFormat.fractionalBits =
        config.productFormat.fractionalBits + discardedWidth)
    (realFits : FitsWidth
      (resultWidth leftWidth rightWidth discardedWidth)
      (HTFFT.Butterfly.Fixed.multiplyRounded config
        (complexValue leftWidth leftReal leftImag)
        (complexValue rightWidth rightReal rightImag)).real)
    (imagFits : FitsWidth
      (resultWidth leftWidth rightWidth discardedWidth)
      (HTFFT.Butterfly.Fixed.multiplyRounded config
        (complexValue leftWidth leftReal leftImag)
        (complexValue rightWidth rightReal rightImag)).imag) :
    interpretSigned
        (_root_.Silean.BitVector.toBitVec
          (resultWidth leftWidth rightWidth discardedWidth)
          (realResultValue leftWidth rightWidth discardedWidth
            leftReal leftImag rightReal rightImag)) =
        (HTFFT.Butterfly.Fixed.multiplyRounded config
          (complexValue leftWidth leftReal leftImag)
          (complexValue rightWidth rightReal rightImag)).real ∧
      interpretSigned
        (_root_.Silean.BitVector.toBitVec
          (resultWidth leftWidth rightWidth discardedWidth)
          (imagResultValue leftWidth rightWidth discardedWidth
            leftReal leftImag rightReal rightImag)) =
        (HTFFT.Butterfly.Fixed.multiplyRounded config
          (complexValue leftWidth leftReal leftImag)
          (complexValue rightWidth rightReal rightImag)).imag := by
  have finish (raw : Int) :
      _root_.Silean.Modules.SignedRoundShift.roundNearestEven
          discardedWidth raw =
        rescale config.rounding
          (config.dataFormat.fractionalBits +
            config.twiddleFormat.fractionalBits)
          config.productFormat.fractionalBits raw := by
    rw [rounding, fractionalBits]
    exact (rescale_nearest_eq_roundNearestEven
      config.productFormat.fractionalBits discardedWidth raw).symm
  have realSpec :
      (HTFFT.Butterfly.Fixed.multiplyRounded config
        (complexValue leftWidth leftReal leftImag)
        (complexValue rightWidth rightReal rightImag)).real =
      _root_.Silean.Modules.SignedRoundShift.roundNearestEven
        discardedWidth
        (_root_.HTFFT.Silean.PipelinedSignedComplexMultiply.realNumerator
          leftWidth rightWidth leftReal leftImag rightReal rightImag) := by
    simp only [HTFFT.Butterfly.Fixed.multiplyRounded, complexValue]
    rw [finish]
    rfl
  have imagSpec :
      (HTFFT.Butterfly.Fixed.multiplyRounded config
        (complexValue leftWidth leftReal leftImag)
        (complexValue rightWidth rightReal rightImag)).imag =
      _root_.Silean.Modules.SignedRoundShift.roundNearestEven
        discardedWidth
        (_root_.HTFFT.Silean.PipelinedSignedComplexMultiply.imagNumerator
          leftWidth rightWidth leftReal leftImag rightReal rightImag) := by
    simp only [HTFFT.Butterfly.Fixed.multiplyRounded, complexValue]
    rw [finish]
    rfl
  constructor
  · rw [realSpec] at realFits ⊢
    unfold _root_.HTFFT.Silean.PipelinedSignedComplexMultiply.realResultValue
    exact interpret_roundedValue_of_fits
      leftWidth rightWidth discardedWidth _ realFits
  · rw [imagSpec] at imagFits ⊢
    unfold _root_.HTFFT.Silean.PipelinedSignedComplexMultiply.imagResultValue
    exact interpret_roundedValue_of_fits
      leftWidth rightWidth discardedWidth _ imagFits

/-- The fixed-point agreement theorem lifted through the structural trace:
every valid delayed output is the pure rounded complex product of its source
input, provided that result is representable at the hardware result width. -/
theorem output_eq_multiplyRounded_of_execution
    (config : HTFFT.Butterfly.Fixed.Config)
    (leftWidth rightWidth discardedWidth : Nat) (pipeline : Pipeline)
    {initialState finalState :
      (_root_.HTFFT.Silean.PipelinedSignedComplexMultiply.moduleStructure
        leftWidth rightWidth discardedWidth pipeline.multiplierLatency
          pipeline.registerBeforeRounding).State}
    {inputs : List
      (_root_.HTFFT.Silean.PipelinedSignedComplexMultiply.ports
        leftWidth rightWidth discardedWidth).inputs.Values}
    {outputs : List
      (_root_.HTFFT.Silean.PipelinedSignedComplexMultiply.ports
        leftWidth rightWidth discardedWidth).outputs.Values}
    (execution :
      (_root_.HTFFT.Silean.PipelinedSignedComplexMultiply.moduleStructure
        leftWidth rightWidth discardedWidth pipeline.multiplierLatency
          pipeline.registerBeforeRounding).Executes
            initialState inputs outputs finalState)
    (t : Nat) (inputInTrace : t < inputs.length)
    (outputInTrace : t + pipeline.latency < outputs.length)
    (rounding : config.rounding = .nearestTiesToEven)
    (fractionalBits :
      config.dataFormat.fractionalBits +
          config.twiddleFormat.fractionalBits =
        config.productFormat.fractionalBits + discardedWidth)
    (realFits : FitsWidth
      (resultWidth leftWidth rightWidth discardedWidth)
      (HTFFT.Butterfly.Fixed.multiplyRounded config
        (complexValue leftWidth
          (inputs.get ⟨t, inputInTrace⟩ .leftReal)
          (inputs.get ⟨t, inputInTrace⟩ .leftImag))
        (complexValue rightWidth
          (inputs.get ⟨t, inputInTrace⟩ .rightReal)
          (inputs.get ⟨t, inputInTrace⟩ .rightImag))).real)
    (imagFits : FitsWidth
      (resultWidth leftWidth rightWidth discardedWidth)
      (HTFFT.Butterfly.Fixed.multiplyRounded config
        (complexValue leftWidth
          (inputs.get ⟨t, inputInTrace⟩ .leftReal)
          (inputs.get ⟨t, inputInTrace⟩ .leftImag))
        (complexValue rightWidth
          (inputs.get ⟨t, inputInTrace⟩ .rightReal)
          (inputs.get ⟨t, inputInTrace⟩ .rightImag))).imag) :
    interpretSigned
        (_root_.Silean.BitVector.toBitVec
          (resultWidth leftWidth rightWidth discardedWidth)
          (outputs.get ⟨t + pipeline.latency, outputInTrace⟩ .resultReal)) =
        (HTFFT.Butterfly.Fixed.multiplyRounded config
          (complexValue leftWidth
            (inputs.get ⟨t, inputInTrace⟩ .leftReal)
            (inputs.get ⟨t, inputInTrace⟩ .leftImag))
          (complexValue rightWidth
            (inputs.get ⟨t, inputInTrace⟩ .rightReal)
            (inputs.get ⟨t, inputInTrace⟩ .rightImag))).real ∧
      interpretSigned
        (_root_.Silean.BitVector.toBitVec
          (resultWidth leftWidth rightWidth discardedWidth)
          (outputs.get ⟨t + pipeline.latency, outputInTrace⟩ .resultImag)) =
        (HTFFT.Butterfly.Fixed.multiplyRounded config
          (complexValue leftWidth
            (inputs.get ⟨t, inputInTrace⟩ .leftReal)
            (inputs.get ⟨t, inputInTrace⟩ .leftImag))
          (complexValue rightWidth
            (inputs.get ⟨t, inputInTrace⟩ .rightReal)
            (inputs.get ⟨t, inputInTrace⟩ .rightImag))).imag := by
  have contract := _root_.Silean.FixedLatency.relation_at_of_trace execution
    (_root_.HTFFT.Silean.PipelinedSignedComplexMultiply.contract_of_execution
      leftWidth rightWidth discardedWidth pipeline execution)
    t inputInTrace outputInTrace
  have values := resultValues_eq_multiplyRounded config
    leftWidth rightWidth discardedWidth
    (inputs.get ⟨t, inputInTrace⟩ .leftReal)
    (inputs.get ⟨t, inputInTrace⟩ .leftImag)
    (inputs.get ⟨t, inputInTrace⟩ .rightReal)
    (inputs.get ⟨t, inputInTrace⟩ .rightImag)
    rounding fractionalBits realFits imagFits
  rw [contract.1, contract.2]
  exact values

end HTFFT.Silean.PipelinedSignedComplexMultiply
