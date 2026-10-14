import Silean.Foundation.BitVector

/-! # Shared fixed-width arithmetic semantics

Natural integer interpretations shared by the public arithmetic modules.  A
result remains an untyped bit vector: signedness describes how each input is
interpreted for this operation, not a persistent property of the output.
-/

namespace Silean.Modules.Arithmetic

open Silean

/-- The result width selected by the arithmetic module families.  Extending
adds one bit beyond the wider operand; truncating retains the wider width. -/
def resultWidth (leftWidth rightWidth : Nat) (extendOutput : Bool) : Nat :=
  max leftWidth rightWidth + if extendOutput then 1 else 0

/-- Interpret a bit vector as either a two's-complement integer or an unsigned
natural number embedded in the integers. -/
def operandValue (signed : Bool) (width : Nat)
    (bits : Fin width → Bool) : Int :=
  let packed := BitVector.toBitVec width bits
  if signed then packed.toInt else packed.toNat

/-- Encode an integer at an explicitly selected result width. -/
def encode (width : Nat) (value : Int) : Fin width → Bool :=
  BitVector.ofBitVec (BitVec.ofInt width value)

end Silean.Modules.Arithmetic
