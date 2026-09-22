import Silean.Foundation.BitVector

namespace SileanTests.BitVector

open Silean

def bits (width value : Nat) : Fin width → Bool :=
  Silean.BitVector.ofNat width value

-- Width zero is a genuine singleton on both sides of the bridge.
#guard (Silean.BitVector.toBitVec 0 (bits 0 7)).toNat == 0
#guard Silean.BitVector.toNat 0
  (Silean.BitVector.ofBitVec (BitVec.ofNat 0 7)) == 0

-- Packing and unpacking use the same least-significant-bit-first order.
#guard Silean.BitVector.toBitVec 4 (bits 4 11) == BitVec.ofNat 4 11
#guard Silean.BitVector.toNat 4
  (Silean.BitVector.ofBitVec (BitVec.ofNat 4 11)) == 11
#guard (Silean.BitVector.ofBitVec (BitVec.ofNat 4 11)) 0
#guard (Silean.BitVector.ofBitVec (BitVec.ofNat 4 11)) 3

-- Both representations apply the same fixed-width truncation.
#guard Silean.BitVector.toBitVec 4 (bits 4 27) == BitVec.ofNat 4 27

example (width : Nat) (value : Fin width → Bool) :
    Silean.BitVector.ofBitVec (Silean.BitVector.toBitVec width value) = value := by
  simp

example (value : BitVec width) :
    Silean.BitVector.toBitVec width (Silean.BitVector.ofBitVec value) = value := by
  simp

example (width : Nat) (value : Fin width → Bool) :
    (Silean.BitVector.toBitVec width value).toNat =
      Silean.BitVector.toNat width value := by
  simp

example (value : BitVec width) :
    Silean.BitVector.toNat width (Silean.BitVector.ofBitVec value) =
      value.toNat := by
  simp

end SileanTests.BitVector
