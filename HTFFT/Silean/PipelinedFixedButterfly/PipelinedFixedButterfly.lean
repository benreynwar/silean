import HTFFT.Butterfly
import HTFFT.Silean.PipelinedSignedComplexMultiply.PipelinedSignedComplexMultiply
import Silean.Authoring.ModulePorts
import Silean.Foundation.BitVector
import Silean.Semantics.FixedLatency

/-! # Pipelined fixed-point radix-two butterfly

This file fixes the public boundary and natural trace contract before any
structural implementation is introduced.  Each packed complex value stores
its imaginary component in the low half and its real component in the high
half, matching the HTFFT hardware convention.

The arithmetic policy is deliberately simple:

* the complex product is formed with fused full-precision numerators and
  rounded once to the input data binary point;
* that rounded product is encoded at the input component width, so this is the
  explicit product wrap boundary from `Butterfly.Fixed.Config.initial`;
* the final upper and lower Add/Sub operations grow each component by exactly
  one high bit; and
* no additional low bits are discarded at this stage.

Consequently a stage with `w`-bit input components has `(w + 1)`-bit output
components with the same fractional-bit count.  A future width schedule may
choose a separate low-bit reduction between stages; it is not part of this
module.
-/

namespace HTFFT.Silean.PipelinedFixedButterfly

open _root_.Silean
open HTFFT.FixedPoint

/-- Static pipeline boundaries of the complete butterfly.

The input register is synchronized across `a`, `b`, and the twiddle.  The
post-product register is synchronized across both components of the completed
rounded and narrowed complex product.  The output register is synchronized
across all four result components. -/
structure Pipeline where
  registerInputs : Bool
  complexMultiply :
    HTFFT.Silean.PipelinedSignedComplexMultiply.Pipeline
  registerProduct : Bool
  registerOutputs : Bool
deriving DecidableEq, Repr

/-- End-to-end latency of the selected butterfly pipeline. -/
def Pipeline.latency (pipeline : Pipeline) : Nat :=
  Bool.toNat pipeline.registerInputs +
    HTFFT.Silean.PipelinedSignedComplexMultiply.Pipeline.latency
      pipeline.complexMultiply +
    Bool.toNat pipeline.registerProduct +
    Bool.toNat pipeline.registerOutputs

/-- The pure fixed-point configuration implemented by one hardware stage. -/
def fixedConfig (dataFormat twiddleFormat : Format) :
    HTFFT.Butterfly.Fixed.Config :=
  HTFFT.Butterfly.Fixed.Config.initial
    dataFormat.width dataFormat.fractionalBits
    twiddleFormat.width twiddleFormat.fractionalBits

/-- Each output component grows by one high bit. -/
def outputComponentWidth (dataFormat : Format) : Nat :=
  _root_.Silean.Modules.Arithmetic.resultWidth
    dataFormat.width dataFormat.width true

@[simp] theorem outputComponentWidth_eq (dataFormat : Format) :
    outputComponentWidth dataFormat = dataFormat.width + 1 := by
  simp [outputComponentWidth,
    _root_.Silean.Modules.Arithmetic.resultWidth]

/-- Static condition under which the generic complex multiplier's rounded
result carrier contains every bit of the selected data-width product boundary.
This condition is about carrier width, not numerical overflow. -/
def ProductCarrierCoversData (dataFormat twiddleFormat : Format) : Prop :=
  dataFormat.width ≤
    HTFFT.Silean.PipelinedSignedComplexMultiply.resultWidth
      dataFormat.width twiddleFormat.width twiddleFormat.fractionalBits

/-- Ordinary fixed-point twiddle formats automatically provide a wide enough
generic multiplier carrier for the explicit data-width product boundary. -/
theorem productCarrierCoversData_of_fractionalBits_le_width
    (dataFormat twiddleFormat : Format)
    (validTwiddle : twiddleFormat.fractionalBits ≤ twiddleFormat.width) :
    ProductCarrierCoversData dataFormat twiddleFormat := by
  simp [ProductCarrierCoversData,
    HTFFT.Silean.PipelinedSignedComplexMultiply.resultWidth,
    HTFFT.Silean.PipelinedSignedComplexMultiply.numeratorWidth,
    HTFFT.Silean.PipelinedSignedComplexMultiply.productWidth,
    _root_.Silean.Modules.Arithmetic.resultWidth]
  omega

/-- Select the low component of a packed complex value. -/
def lowComponent (componentWidth : Nat)
    (value : Fin (componentWidth + componentWidth) → Bool) :
    Fin componentWidth → Bool :=
  fun index => value (Fin.castAdd componentWidth index)

/-- Select the high component of a packed complex value. -/
def highComponent (componentWidth : Nat)
    (value : Fin (componentWidth + componentWidth) → Bool) :
    Fin componentWidth → Bool :=
  fun index => value (Fin.natAdd componentWidth index)

/-- Decode a packed two's-complement complex value.  The imaginary component
occupies the low half and the real component the high half. -/
def decodeComplex (componentWidth : Nat)
    (value : Fin (componentWidth + componentWidth) → Bool) :
    HTFFT.Complex Int :=
  { real := interpretSigned
      (BitVector.toBitVec componentWidth
        (highComponent componentWidth value))
    imag := interpretSigned
      (BitVector.toBitVec componentWidth
        (lowComponent componentWidth value)) }

@[simp] theorem wrapComplex_decodeComplex (format : Format)
    (value : Fin (format.width + format.width) → Bool) :
    HTFFT.Butterfly.Fixed.wrapComplex format
        (decodeComplex format.width value) =
      decodeComplex format.width value := by
  simp [HTFFT.Butterfly.Fixed.wrapComplex, HTFFT.Complex.map,
    decodeComplex]

/-- Encode a signed integer component modulo the selected width. -/
def encodeComponent (componentWidth : Nat) (value : Int) :
    Fin componentWidth → Bool :=
  BitVector.ofBitVec (encodeSigned componentWidth value)

@[simp] theorem encodeComponent_wrapSigned (componentWidth : Nat)
    (value : Int) :
    encodeComponent componentWidth (wrapSigned componentWidth value) =
      encodeComponent componentWidth value := by
  unfold encodeComponent
  rw [← interpretSigned_encodeSigned componentWidth value,
    encodeSigned_interpretSigned]

/-- Encode a complex integer value in the public packed layout. -/
def encodeComplex (componentWidth : Nat) (value : HTFFT.Complex Int) :
    Fin (componentWidth + componentWidth) → Bool :=
  Fin.addCases
    (encodeComponent componentWidth value.imag)
    (encodeComponent componentWidth value.real)

@[simp] theorem lowComponent_encodeComplex (componentWidth : Nat)
    (value : HTFFT.Complex Int) :
    lowComponent componentWidth (encodeComplex componentWidth value) =
      encodeComponent componentWidth value.imag := by
  funext index
  simp [lowComponent, encodeComplex]

@[simp] theorem highComponent_encodeComplex (componentWidth : Nat)
    (value : HTFFT.Complex Int) :
    highComponent componentWidth (encodeComplex componentWidth value) =
      encodeComponent componentWidth value.real := by
  funext index
  change Fin.addCases
      (encodeComponent componentWidth value.imag)
      (encodeComponent componentWidth value.real)
      (Fin.natAdd componentWidth index) =
    encodeComponent componentWidth value.real index
  exact Fin.addCases_right index

@[simp] theorem decodeComplex_encodeComplex (componentWidth : Nat)
    (value : HTFFT.Complex Int) :
    decodeComplex componentWidth (encodeComplex componentWidth value) =
      HTFFT.Butterfly.Fixed.wrapComplex
        ⟨componentWidth, 0⟩ value := by
  simp [decodeComplex, encodeComponent,
    HTFFT.Butterfly.Fixed.wrapComplex, HTFFT.Complex.map,
    interpretSigned, encodeSigned, wrapSigned]

/-- Re-encoding the signed interpretation of an existing packed complex word
recovers every bit of that word. -/
@[simp] theorem encodeComplex_decodeComplex (componentWidth : Nat)
    (value : Fin (componentWidth + componentWidth) → Bool) :
    encodeComplex componentWidth (decodeComplex componentWidth value) =
      value := by
  funext index
  refine Fin.addCases ?_ ?_ index
  · intro low
    simp [encodeComplex, encodeComponent, decodeComplex, lowComponent]
  · intro high
    simp only [encodeComplex, encodeComponent, decodeComplex,
      encodeSigned_interpretSigned, BitVector.ofBitVec_toBitVec]
    rw [Fin.addCases_right]
    rfl

@[simp] theorem encodeComplex_wrapComplex (format : Format)
    (value : HTFFT.Complex Int) :
    encodeComplex format.width
        (HTFFT.Butterfly.Fixed.wrapComplex format value) =
      encodeComplex format.width value := by
  unfold HTFFT.Butterfly.Fixed.wrapComplex HTFFT.Complex.map encodeComplex
  simp

/-- Pure result associated with one packed butterfly input. -/
def resultValue (dataFormat twiddleFormat : Format)
    (a b : Fin (dataFormat.width + dataFormat.width) → Bool)
    (twiddle : Fin (twiddleFormat.width + twiddleFormat.width) → Bool) :
    HTFFT.Butterfly.Result Int :=
  HTFFT.Butterfly.Fixed.butterfly (fixedConfig dataFormat twiddleFormat)
    (decodeComplex dataFormat.width a)
    (decodeComplex dataFormat.width b)
    (decodeComplex twiddleFormat.width twiddle)

module_ports ports (dataFormat : Format) (twiddleFormat : Format) where
  input a : .vector (dataFormat.width + dataFormat.width) .bit,
  input b : .vector (dataFormat.width + dataFormat.width) .bit,
  input twiddle : .vector
    (twiddleFormat.width + twiddleFormat.width) .bit,
  output upper : .vector
    (outputComponentWidth dataFormat + outputComponentWidth dataFormat) .bit,
  output lower : .vector
    (outputComponentWidth dataFormat + outputComponentWidth dataFormat) .bit

/-- Every available delayed output is exactly the packed pure fixed-point
butterfly result of its corresponding packed input. -/
def contract (dataFormat twiddleFormat : Format) (pipeline : Pipeline)
    (trace : BoundaryTrace (ports dataFormat twiddleFormat)) : Prop :=
  FixedLatency.Holds pipeline.latency
    (fun
      (input : (ports dataFormat twiddleFormat).inputs.Values)
      (output : (ports dataFormat twiddleFormat).outputs.Values) =>
      let result := resultValue dataFormat twiddleFormat
        (input .a) (input .b) (input .twiddle)
      output .upper =
          encodeComplex (outputComponentWidth dataFormat) result.upper ∧
        output .lower =
          encodeComplex (outputComponentWidth dataFormat) result.lower)
    trace

end HTFFT.Silean.PipelinedFixedButterfly
