import HTFFT.Complex

namespace HTFFT.FixedPoint

/-! Pure scaled-integer fixed-point semantics. Width affects only
representability and an explicitly requested overflow operation; ordinary
arithmetic is performed in unbounded `Int`. -/

structure Format where
  width : Nat
  fractionalBits : Nat
  deriving Repr, DecidableEq

/-- The integer scale associated with a format. A raw integer `x` represents
`x / scale`. -/
def Format.scale (format : Format) : Nat := 2 ^ format.fractionalBits

/-- The exact rational value of one least-significant bit in a format. -/
def Format.quantum (format : Format) : Rat :=
  Rat.divInt 1 format.scale

/-- The least integer represented by a two's-complement word of this width.
Width zero denotes the single value zero. -/
def signedMin : Nat → Int
  | 0 => 0
  | width + 1 => -((2 ^ width : Nat) : Int)

/-- The greatest integer represented by a two's-complement word of this width.
Width zero denotes the single value zero. -/
def signedMax : Nat → Int
  | 0 => 0
  | width + 1 => ((2 ^ width : Nat) : Int) - 1

def FitsWidth (width : Nat) (raw : Int) : Prop :=
  signedMin width ≤ raw ∧ raw ≤ signedMax width

def Fits (format : Format) (raw : Int) : Prop :=
  FitsWidth format.width raw

def ComplexFits (format : Format) (value : HTFFT.Complex Int) : Prop :=
  Fits format value.real ∧ Fits format value.imag

/-- The explicit boundary from a two's-complement bit pattern to the scaled
integer used by the pure specification. -/
def interpretSigned {width : Nat} (bits : BitVec width) : Int :=
  bits.toInt

/-- Encode an integer modulo `2^width`. Decoding this value is exactly
`wrapSigned width raw`, as recorded below. -/
def encodeSigned (width : Nat) (raw : Int) : BitVec width :=
  BitVec.ofInt width raw

/-- Interpret a scaled integer as an exact rational value. -/
def decode (format : Format) (raw : Int) : Rat :=
  Rat.divInt raw format.scale

def decodeComplex (format : Format)
    (value : HTFFT.Complex Int) : HTFFT.Complex Rat :=
  value.map (decode format)

/-! Rounding is named independently of multiplication so the same operation
can specify input quantization, format conversion, and product rescaling. -/

inductive RoundingMode where
  /-- Round toward negative infinity. For a power-of-two divisor this matches
  an arithmetic right shift. -/
  | towardNegative
  /-- Discard the fractional part toward zero. -/
  | towardZero
  /-- Round to the nearest integer; an exact half is sent to the even integer. -/
  | nearestTiesToEven
  deriving Repr, DecidableEq

/-- Divide by a positive natural denominator according to the selected rule.
The zero-denominator branch is total but is not used by fixed-point formats. -/
def roundRatio (mode : RoundingMode) (numerator : Int)
    (denominator : Nat) : Int :=
  if denominator = 0 then
    0
  else
    let divisor : Int := denominator
    match mode with
    | .towardNegative => numerator / divisor
    | .towardZero => numerator.tdiv divisor
    | .nearestTiesToEven =>
        let lower := numerator / divisor
        let remainder := numerator % divisor
        let comparison := 2 * remainder
        if comparison < divisor then
          lower
        else if divisor < comparison then
          lower + 1
        else if lower % 2 = 0 then
          lower
        else
          lower + 1

/-- Quantize an exact rational to a scaled integer. Overflow is deliberately
separate: this result can record that a chosen format is too narrow. -/
def encode (mode : RoundingMode) (format : Format) (value : Rat) : Int :=
  roundRatio mode (value.num * format.scale) value.den

def encodeComplex (mode : RoundingMode) (format : Format)
    (value : HTFFT.Complex Rat) : HTFFT.Complex Int :=
  value.map (encode mode format)

/-- Change the binary-point position of a scaled integer. This does not apply
the destination width. -/
def rescale (mode : RoundingMode) (sourceFractionalBits : Nat)
    (destinationFractionalBits : Nat) (raw : Int) : Int :=
  if sourceFractionalBits ≤ destinationFractionalBits then
    raw * (2 ^ (destinationFractionalBits - sourceFractionalBits) : Nat)
  else
    roundRatio mode raw (2 ^ (sourceFractionalBits - destinationFractionalBits))

@[simp] theorem rescale_same (mode : RoundingMode) (fractionalBits : Nat)
    (raw : Int) :
    rescale mode fractionalBits fractionalBits raw = raw := by
  simp [rescale]

/-- Two's-complement wrapping into `width` bits, returned as its signed integer
interpretation. -/
def wrapSigned (width : Nat) (raw : Int) : Int :=
  raw.bmod (2 ^ width)

@[simp] theorem interpretSigned_encodeSigned (width : Nat) (raw : Int) :
    interpretSigned (encodeSigned width raw) = wrapSigned width raw := by
  simp [interpretSigned, encodeSigned, wrapSigned]

@[simp] theorem encodeSigned_interpretSigned {width : Nat}
    (bits : BitVec width) :
    encodeSigned width (interpretSigned bits) = bits := by
  simp [interpretSigned, encodeSigned]

/-- Interpreting an existing signed word is already canonical for its width. -/
@[simp] theorem wrapSigned_interpretSigned {width : Nat}
    (bits : BitVec width) :
    wrapSigned width (interpretSigned bits) = interpretSigned bits := by
  rw [← interpretSigned_encodeSigned width (interpretSigned bits),
    encodeSigned_interpretSigned]

/-- Applying the same explicit signed wrapping boundary twice is idempotent. -/
@[simp] theorem wrapSigned_wrapSigned (width : Nat) (raw : Int) :
    wrapSigned width (wrapSigned width raw) = wrapSigned width raw := by
  rw [← interpretSigned_encodeSigned width raw,
    wrapSigned_interpretSigned]

end HTFFT.FixedPoint
