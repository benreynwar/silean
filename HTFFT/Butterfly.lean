import HTFFT.FixedPoint

namespace HTFFT.Butterfly

structure Result (α : Type) where
  upper : HTFFT.Complex α
  lower : HTFFT.Complex α
  deriving Repr, DecidableEq

/-- The mathematical radix-two butterfly. This definition contains no
fixed-point formats, rounding, overflow, latency, or hardware layout. -/
def mathematical [Add α] [Sub α] [Mul α]
    (a b twiddle : HTFFT.Complex α) : Result α :=
  let twiddled := b * twiddle
  { upper := a + twiddled
    lower := a - twiddled }

namespace Fixed

open HTFFT.FixedPoint

/-- Every precision-changing boundary in the intended fixed-point butterfly is
named explicitly. `productFormat` is the stored result of twiddle
multiplication and is also the working format used by the final additions. -/
structure Config where
  dataFormat : Format
  twiddleFormat : Format
  productFormat : Format
  outputFormat : Format
  rounding : RoundingMode
  deriving Repr, DecidableEq

/-- The approved initial policy: retain the data binary point, round the fused
complex product to nearest with ties to even, and grow the final result by one
component bit. Wrap remains explicit even though later range hypotheses should
show that it is not exercised. -/
def Config.initial (dataWidth dataFractionalBits twiddleWidth
    twiddleFractionalBits : Nat) : Config :=
  { dataFormat := ⟨dataWidth, dataFractionalBits⟩
    twiddleFormat := ⟨twiddleWidth, twiddleFractionalBits⟩
    productFormat := ⟨dataWidth, dataFractionalBits⟩
    outputFormat := ⟨dataWidth + 1, dataFractionalBits⟩
    rounding := .nearestTiesToEven }

def rescaleComplex (rounding : RoundingMode) (source destination : Format)
    (value : HTFFT.Complex Int) : HTFFT.Complex Int :=
  value.map (rescale rounding source.fractionalBits destination.fractionalBits)

def wrapComplex (format : Format)
    (value : HTFFT.Complex Int) : HTFFT.Complex Int :=
  value.map (wrapSigned format.width)

@[simp] theorem wrapComplex_wrapComplex (format : Format)
    (value : HTFFT.Complex Int) :
    wrapComplex format (wrapComplex format value) = wrapComplex format value := by
  cases value
  simp [wrapComplex, HTFFT.Complex.map]

/-- Complex multiplication forms each real or imaginary numerator at full
integer precision and rounds only after its two terms have been combined. The
result has not yet had its destination width applied. -/
def multiplyRounded (config : Config) (left twiddle : HTFFT.Complex Int) :
    HTFFT.Complex Int :=
  let sourceFractionalBits :=
    config.dataFormat.fractionalBits + config.twiddleFormat.fractionalBits
  let finish (raw : Int) : Int :=
    rescale config.rounding sourceFractionalBits
      config.productFormat.fractionalBits raw
  { real := finish
      (left.real * twiddle.real - left.imag * twiddle.imag)
    imag := finish
      (left.real * twiddle.imag + left.imag * twiddle.real) }

def multiply (config : Config) (left twiddle : HTFFT.Complex Int) :
    HTFFT.Complex Int :=
  wrapComplex config.productFormat
    (multiplyRounded config left twiddle)

@[simp] theorem wrapComplex_multiply (config : Config)
    (left twiddle : HTFFT.Complex Int) :
    wrapComplex config.productFormat (multiply config left twiddle) =
      multiply config left twiddle := by
  simp [multiply]

def alignedARounded (config : Config) (a : HTFFT.Complex Int) :
    HTFFT.Complex Int :=
  rescaleComplex config.rounding config.dataFormat config.productFormat a

def alignedA (config : Config) (a : HTFFT.Complex Int) :
    HTFFT.Complex Int :=
  wrapComplex config.productFormat
    (alignedARounded config a)

@[simp] theorem wrapComplex_alignedA (config : Config)
    (a : HTFFT.Complex Int) :
    wrapComplex config.productFormat (alignedA config a) =
      alignedA config a := by
  simp [alignedA]

/-- Both outputs after their final rescaling but before output overflow. -/
def outputRounded (config : Config) (a b twiddle : HTFFT.Complex Int) :
    Result Int :=
  let preparedA := alignedA config a
  let twiddled := multiply config b twiddle
  { upper := rescaleComplex config.rounding config.productFormat
      config.outputFormat (preparedA + twiddled)
    lower := rescaleComplex config.rounding config.productFormat
      config.outputFormat (preparedA - twiddled) }

/-- The pure fixed-point butterfly specification. All arithmetic is ordinary
Lean integer arithmetic; widths take effect only at the explicit conversion
and overflow boundaries above. -/
def butterfly (config : Config) (a b twiddle : HTFFT.Complex Int) :
    Result Int :=
  let rounded := outputRounded config a b twiddle
  { upper := wrapComplex config.outputFormat rounded.upper
    lower := wrapComplex config.outputFormat rounded.lower }

/-- Concrete hypotheses under which none of the fixed-width boundaries changes
its mathematical integer input. This is the expected range side-condition for
the first accuracy proof. -/
def NoOverflow (config : Config) (a b twiddle : HTFFT.Complex Int) : Prop :=
  ComplexFits config.dataFormat a ∧
  ComplexFits config.dataFormat b ∧
  ComplexFits config.twiddleFormat twiddle ∧
  ComplexFits config.productFormat (alignedARounded config a) ∧
  ComplexFits config.productFormat (multiplyRounded config b twiddle) ∧
  let rounded := outputRounded config a b twiddle
  ComplexFits config.outputFormat rounded.upper ∧
  ComplexFits config.outputFormat rounded.lower

def decodeResult (config : Config) (result : Result Int) : Result Rat :=
  { upper := decodeComplex config.outputFormat result.upper
    lower := decodeComplex config.outputFormat result.lower }

/-- The exact result against which local arithmetic error will be measured.
Inputs are the exact rational values denoted by their supplied scaled integers;
input and twiddle quantization error therefore remain separate terms. -/
def exactDecodedInputs (config : Config) (a b twiddle : HTFFT.Complex Int) :
    Result Rat :=
  mathematical
    (decodeComplex config.dataFormat a)
    (decodeComplex config.dataFormat b)
    (decodeComplex config.twiddleFormat twiddle)

def rationalAbs (value : Rat) : Rat :=
  if value < 0 then -value else value

def componentwiseWithin (bound : Rat) (actual expected : HTFFT.Complex Rat) : Prop :=
  rationalAbs (actual.real - expected.real) ≤ bound ∧
  rationalAbs (actual.imag - expected.imag) ≤ bound

def resultWithin (bound : Rat) (actual expected : Result Rat) : Prop :=
  componentwiseWithin bound actual.upper expected.upper ∧
  componentwiseWithin bound actual.lower expected.lower

/-- Shape of the later local numerical theorem. The explicit no-wrap
hypothesis prevents modular fixed-width semantics from being confused with a
small numerical approximation error. -/
def HasLocalErrorBound (config : Config) (bound : Rat) : Prop :=
  0 ≤ bound ∧
  ∀ a b twiddle, NoOverflow config a b twiddle →
    resultWithin bound
      (decodeResult config (butterfly config a b twiddle))
      (exactDecodedInputs config a b twiddle)

end Fixed

end HTFFT.Butterfly
