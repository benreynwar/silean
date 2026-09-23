import HTFFT.Silean.UnrolledFFT.Configuration
import Silean.Authoring.ModulePorts
import Silean.Semantics.FixedLatency

/-! # One unrolled FFT layer

The public contract is a natural vector-level statement.  It says that the
layer applies `HTFFT.Fixed.butterflyLayer` after the common latency of its
parallel butterflies.  Child instances, static twiddle sources, splitting,
and combining belong to the structural implementation.
-/

namespace HTFFT.Silean.UnrolledFFTLayer

open _root_.Silean
open HTFFT.FixedPoint

/-- Packed hardware type of one complex sample in a selected format. -/
def complexSignalType (format : Format) : SignalType :=
  .vector (format.width + format.width) .bit

/-- Decode every packed sample into the ordinary integer vector used by the
pure fixed-point FFT. -/
def decodeVector (format : Format)
    (values : Fin (2 ^ depth) → (complexSignalType format).Denote) :
    HTFFT.Fixed.Vector depth :=
  fun index => PipelinedFixedButterfly.decodeComplex format.width (values index)

/-- Encode every pure fixed-point sample into the packed hardware layout. -/
def encodeVector (format : Format) (values : HTFFT.Fixed.Vector depth) :
    Fin (2 ^ depth) → (complexSignalType format).Denote :=
  fun index => PipelinedFixedButterfly.encodeComplex format.width (values index)

/-- Decoding a packed vector returns the canonical signed representative of
each component at the selected width. -/
@[simp] theorem decodeVector_encodeVector (format : Format)
    (values : HTFFT.Fixed.Vector depth) :
    decodeVector format (encodeVector format values) =
      fun index => HTFFT.Butterfly.Fixed.wrapComplex format (values index) := by
  funext index
  simp [decodeVector, encodeVector,
    HTFFT.Butterfly.Fixed.wrapComplex, HTFFT.Complex.map]

/-- Packing after decoding is the identity on hardware sample vectors. -/
@[simp] theorem encodeVector_decodeVector (format : Format)
    (values : Fin (2 ^ depth) → (complexSignalType format).Denote) :
    encodeVector format (decodeVector format values) = values := by
  funext index
  simp [encodeVector, decodeVector]

/-- Natural vector result of one hardware layer. -/
def resultValue (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (stage : Fin depth)
    (input : Fin (2 ^ depth) →
      (complexSignalType
        (configuration.boundaryFormat stage.castSucc)).Denote) :
    HTFFT.Fixed.Vector depth :=
  HTFFT.Fixed.butterflyLayer configuration.fixedConfig table stage
    (decodeVector (configuration.boundaryFormat stage.castSucc) input)

/-- A layer result survives the packed boundary round-trip exactly because
the pure fixed-point layer already applies its explicit output wrap. -/
@[simp] theorem decodeVector_encodeVector_resultValue
    (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (stage : Fin depth)
    (input : Fin (2 ^ depth) →
      (complexSignalType
        (configuration.boundaryFormat stage.castSucc)).Denote) :
    decodeVector (configuration.boundaryFormat stage.succ)
        (encodeVector (configuration.boundaryFormat stage.succ)
          (resultValue configuration table stage input)) =
      resultValue configuration table stage input := by
  rw [decodeVector_encodeVector]
  exact HTFFT.Fixed.wrapComplex_butterflyLayer
    configuration.fixedConfig table stage _

module_ports ports (configuration : UnrolledFFT.Configuration depth)
    (stage : Fin depth) where
  input input : .vector (2 ^ depth)
    (complexSignalType (configuration.boundaryFormat stage.castSucc)),
  output output : .vector (2 ^ depth)
    (complexSignalType (configuration.boundaryFormat stage.succ))

/-- Every available layer output is the packed pure fixed-point layer result
for the corresponding input cycle. -/
def contract (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (stage : Fin depth)
    (trace : BoundaryTrace (ports configuration stage)) : Prop :=
  FixedLatency.Holds (configuration.layerLatency stage)
    (fun
      (input : (ports configuration stage).inputs.Values)
      (output : (ports configuration stage).outputs.Values) =>
      output .output =
        encodeVector (configuration.boundaryFormat stage.succ)
          (resultValue configuration table stage (input .input)))
    trace

end HTFFT.Silean.UnrolledFFTLayer
