import HTFFT.Silean.PipelinedFixedButterfly.PipelinedFixedButterfly
import HTFFT.Silean.PipelinedSignedComplexMultiply
import Silean.Modules.VectorLayout.Extensions

/-! Bit-level arithmetic bridges for the structural butterfly proof. -/

namespace HTFFT.Silean.PipelinedFixedButterfly.Internal

open _root_.Silean
open _root_.Silean.Modules
open HTFFT.FixedPoint
open HTFFT.Silean.PipelinedSignedComplexMultiply

/-- Apply the explicit data-width product boundary to one result component of
the generic complex multiplier. -/
def narrowProductComponent (dataFormat twiddleFormat : Format)
    (value : Fin (resultWidth dataFormat.width
      twiddleFormat.width twiddleFormat.fractionalBits) → Bool) :
    Fin dataFormat.width → Bool :=
  VectorLayout.apply
    (VectorLayout.extensionLayout true
      (resultWidth dataFormat.width
        twiddleFormat.width twiddleFormat.fractionalBits)
      dataFormat.width)
    value

/-- Narrow and pack the two actual outputs of the generic complex multiplier. -/
def packProductOutputs (dataFormat twiddleFormat : Format)
    (resultReal resultImag : Fin (resultWidth dataFormat.width
      twiddleFormat.width twiddleFormat.fractionalBits) → Bool) :
    Fin (dataFormat.width + dataFormat.width) → Bool :=
  Fin.addCases
    (narrowProductComponent dataFormat twiddleFormat resultImag)
    (narrowProductComponent dataFormat twiddleFormat resultReal)

/-- Packed product value at the butterfly's explicit `dataWidth` boundary. -/
def productBoundaryCircuitValue (dataFormat twiddleFormat : Format)
    (bReal bImag : Fin dataFormat.width → Bool)
    (twiddleReal twiddleImag : Fin twiddleFormat.width → Bool) :
    Fin (dataFormat.width + dataFormat.width) → Bool :=
  packProductOutputs dataFormat twiddleFormat
    (realResultValue dataFormat.width twiddleFormat.width
      twiddleFormat.fractionalBits bReal bImag twiddleReal twiddleImag)
    (imagResultValue dataFormat.width twiddleFormat.width
      twiddleFormat.fractionalBits bReal bImag twiddleReal twiddleImag)

/-- The narrowed and packed generic multiplier result is exactly the explicit
wrapped product boundary in the pure fixed-point butterfly. -/
theorem productBoundaryCircuitValue_eq_fixedMultiply
    (dataFormat twiddleFormat : Format)
    (carrier : ProductCarrierCoversData dataFormat twiddleFormat)
    (bReal bImag : Fin dataFormat.width → Bool)
    (twiddleReal twiddleImag : Fin twiddleFormat.width → Bool) :
    productBoundaryCircuitValue dataFormat twiddleFormat
        bReal bImag twiddleReal twiddleImag =
      encodeComplex dataFormat.width
        (HTFFT.Butterfly.Fixed.multiply
          (fixedConfig dataFormat twiddleFormat)
          (complexValue dataFormat.width bReal bImag)
          (complexValue twiddleFormat.width
            twiddleReal twiddleImag)) := by
  let config := fixedConfig dataFormat twiddleFormat
  have encoded := resultValues_eq_encode_multiplyRounded
    config dataFormat.width twiddleFormat.width
      twiddleFormat.fractionalBits bReal bImag twiddleReal twiddleImag
      (by rfl) (by simp [config, fixedConfig,
        HTFFT.Butterfly.Fixed.Config.initial])
  unfold productBoundaryCircuitValue packProductOutputs narrowProductComponent
  rw [encoded.1, encoded.2]
  have realNarrow := VectorLayout.apply_extensionLayout_encodeSigned_of_le
    (resultWidth dataFormat.width twiddleFormat.width
      twiddleFormat.fractionalBits)
    dataFormat.width
    (HTFFT.Butterfly.Fixed.multiplyRounded config
      (complexValue dataFormat.width bReal bImag)
      (complexValue twiddleFormat.width
        twiddleReal twiddleImag)).real
    carrier
  have imagNarrow := VectorLayout.apply_extensionLayout_encodeSigned_of_le
    (resultWidth dataFormat.width twiddleFormat.width
      twiddleFormat.fractionalBits)
    dataFormat.width
    (HTFFT.Butterfly.Fixed.multiplyRounded config
      (complexValue dataFormat.width bReal bImag)
      (complexValue twiddleFormat.width
        twiddleReal twiddleImag)).imag
    carrier
  unfold Arithmetic.encode at realNarrow imagNarrow ⊢
  rw [realNarrow, imagNarrow]
  change encodeComplex dataFormat.width
      (HTFFT.Butterfly.Fixed.multiplyRounded config
        (complexValue dataFormat.width bReal bImag)
        (complexValue twiddleFormat.width twiddleReal twiddleImag)) =
    encodeComplex dataFormat.width
      (HTFFT.Butterfly.Fixed.multiply config
        (complexValue dataFormat.width bReal bImag)
        (complexValue twiddleFormat.width twiddleReal twiddleImag))
  unfold HTFFT.Butterfly.Fixed.multiply
  simp [config, fixedConfig, HTFFT.Butterfly.Fixed.Config.initial]

/-- Combinational upper output produced by the two extended signed adders. -/
def upperCircuitValue (dataFormat : Format)
    (a product : Fin (dataFormat.width + dataFormat.width) → Bool) :
    Fin (outputComponentWidth dataFormat +
      outputComponentWidth dataFormat) → Bool :=
  Fin.addCases
    (Add.resultValue dataFormat.width dataFormat.width true true true
      (lowComponent dataFormat.width a)
      (lowComponent dataFormat.width product))
    (Add.resultValue dataFormat.width dataFormat.width true true true
      (highComponent dataFormat.width a)
      (highComponent dataFormat.width product))

/-- Combinational lower output produced by the two extended signed
subtractors. -/
def lowerCircuitValue (dataFormat : Format)
    (a product : Fin (dataFormat.width + dataFormat.width) → Bool) :
    Fin (outputComponentWidth dataFormat +
      outputComponentWidth dataFormat) → Bool :=
  Fin.addCases
    (Sub.resultValue dataFormat.width dataFormat.width true true true
      (lowComponent dataFormat.width a)
      (lowComponent dataFormat.width product))
    (Sub.resultValue dataFormat.width dataFormat.width true true true
      (highComponent dataFormat.width a)
      (highComponent dataFormat.width product))

theorem upperCircuitValue_eq_encodeComplex (dataFormat : Format)
    (a product : Fin (dataFormat.width + dataFormat.width) → Bool) :
    upperCircuitValue dataFormat a product =
      encodeComplex (outputComponentWidth dataFormat)
        (decodeComplex dataFormat.width a +
          decodeComplex dataFormat.width product) := by
  rfl

theorem lowerCircuitValue_eq_encodeComplex (dataFormat : Format)
    (a product : Fin (dataFormat.width + dataFormat.width) → Bool) :
    lowerCircuitValue dataFormat a product =
      encodeComplex (outputComponentWidth dataFormat)
        (decodeComplex dataFormat.width a -
          decodeComplex dataFormat.width product) := by
  rfl

/-- Once the product has crossed its explicit data-width boundary, the four
extended Add/Sub outputs are exactly the encoded pure butterfly result. -/
theorem addSubCircuitValues_eq_fixedButterfly
    (dataFormat twiddleFormat : Format)
    (a b : Fin (dataFormat.width + dataFormat.width) → Bool)
    (twiddle : Fin (twiddleFormat.width + twiddleFormat.width) → Bool) :
    let config := fixedConfig dataFormat twiddleFormat
    let product := encodeComplex dataFormat.width
      (HTFFT.Butterfly.Fixed.multiply config
        (decodeComplex dataFormat.width b)
        (decodeComplex twiddleFormat.width twiddle))
    upperCircuitValue dataFormat a product =
        encodeComplex (outputComponentWidth dataFormat)
          (resultValue dataFormat twiddleFormat a b twiddle).upper ∧
      lowerCircuitValue dataFormat a product =
        encodeComplex (outputComponentWidth dataFormat)
          (resultValue dataFormat twiddleFormat a b twiddle).lower := by
  let config := fixedConfig dataFormat twiddleFormat
  let decodedA := decodeComplex dataFormat.width a
  let decodedB := decodeComplex dataFormat.width b
  let decodedTwiddle := decodeComplex twiddleFormat.width twiddle
  let product := HTFFT.Butterfly.Fixed.multiply config decodedB decodedTwiddle
  have productCanonical :
      HTFFT.Butterfly.Fixed.wrapComplex ⟨dataFormat.width, 0⟩ product =
        product := by
    simpa [product, config, fixedConfig,
      HTFFT.Butterfly.Fixed.Config.initial,
      HTFFT.Butterfly.Fixed.wrapComplex] using
      (HTFFT.Butterfly.Fixed.wrapComplex_multiply
        config decodedB decodedTwiddle)
  have alignedA : HTFFT.Butterfly.Fixed.alignedA config decodedA = decodedA := by
    simp [config, fixedConfig, HTFFT.Butterfly.Fixed.Config.initial,
      HTFFT.Butterfly.Fixed.alignedA,
      HTFFT.Butterfly.Fixed.alignedARounded,
      HTFFT.Butterfly.Fixed.rescaleComplex,
      HTFFT.Butterfly.Fixed.wrapComplex, HTFFT.Complex.map,
      decodedA, decodeComplex]
  have upperSpec :
      (HTFFT.Butterfly.Fixed.butterfly config decodedA decodedB
          decodedTwiddle).upper =
        HTFFT.Butterfly.Fixed.wrapComplex config.outputFormat
          (decodedA + product) := by
    unfold HTFFT.Butterfly.Fixed.butterfly
      HTFFT.Butterfly.Fixed.outputRounded
    dsimp only
    rw [alignedA]
    change HTFFT.Butterfly.Fixed.wrapComplex config.outputFormat
        (HTFFT.Butterfly.Fixed.rescaleComplex config.rounding
          config.productFormat config.outputFormat (decodedA + product)) = _
    simp [config, fixedConfig, HTFFT.Butterfly.Fixed.Config.initial,
      HTFFT.Butterfly.Fixed.rescaleComplex, HTFFT.Complex.map]
    rfl
  have lowerSpec :
      (HTFFT.Butterfly.Fixed.butterfly config decodedA decodedB
          decodedTwiddle).lower =
        HTFFT.Butterfly.Fixed.wrapComplex config.outputFormat
          (decodedA - product) := by
    unfold HTFFT.Butterfly.Fixed.butterfly
      HTFFT.Butterfly.Fixed.outputRounded
    dsimp only
    rw [alignedA]
    change HTFFT.Butterfly.Fixed.wrapComplex config.outputFormat
        (HTFFT.Butterfly.Fixed.rescaleComplex config.rounding
          config.productFormat config.outputFormat (decodedA - product)) = _
    simp [config, fixedConfig, HTFFT.Butterfly.Fixed.Config.initial,
      HTFFT.Butterfly.Fixed.rescaleComplex, HTFFT.Complex.map]
    rfl
  dsimp only
  constructor
  · rw [upperCircuitValue_eq_encodeComplex]
    change encodeComplex (outputComponentWidth dataFormat)
        (decodedA + decodeComplex dataFormat.width
          (encodeComplex dataFormat.width product)) = _
    rw [decodeComplex_encodeComplex, productCanonical]
    change encodeComplex (outputComponentWidth dataFormat)
        (decodedA + product) =
      encodeComplex (outputComponentWidth dataFormat)
        (HTFFT.Butterfly.Fixed.butterfly config decodedA decodedB
          decodedTwiddle).upper
    rw [upperSpec]
    rw [outputComponentWidth_eq]
    simpa [config, fixedConfig, HTFFT.Butterfly.Fixed.Config.initial] using
      (encodeComplex_wrapComplex config.outputFormat
        (decodedA + product)).symm
  · rw [lowerCircuitValue_eq_encodeComplex]
    change encodeComplex (outputComponentWidth dataFormat)
        (decodedA - decodeComplex dataFormat.width
          (encodeComplex dataFormat.width product)) = _
    rw [decodeComplex_encodeComplex, productCanonical]
    change encodeComplex (outputComponentWidth dataFormat)
        (decodedA - product) =
      encodeComplex (outputComponentWidth dataFormat)
        (HTFFT.Butterfly.Fixed.butterfly config decodedA decodedB
          decodedTwiddle).lower
    rw [lowerSpec]
    rw [outputComponentWidth_eq]
    simpa [config, fixedConfig, HTFFT.Butterfly.Fixed.Config.initial] using
      (encodeComplex_wrapComplex config.outputFormat
        (decodedA - product)).symm

end HTFFT.Silean.PipelinedFixedButterfly.Internal
