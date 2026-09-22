import Silean.Modules.SignedMultiply.SignedMultiply

namespace SileanTests.SignedMultiplyContract

open Silean
open Silean.Modules.SignedMultiply

def signedBits (width : Nat) (value : Int) : Fin width → Bool :=
  BitVector.ofBitVec (BitVec.ofInt width value)

def inputs (leftWidth rightWidth : Nat)
    (left : Fin leftWidth → Bool) (right : Fin rightWidth → Bool) :
    (ports leftWidth rightWidth).inputs.Values
  | .left => left
  | .right => right

def result (leftWidth rightWidth : Nat)
    (left : Fin leftWidth → Bool) (right : Fin rightWidth → Bool) :=
  ((cycleContract leftWidth rightWidth).evaluate
    (inputs leftWidth rightWidth left right) SignalMap.emptyValues).1 .result

def signedValue (width : Nat) (value : Fin width → Bool) : Int :=
  (BitVector.toBitVec width value).toInt

-- A zero-width operand denotes zero while the other operand determines the
-- result width.
#guard signedValue 0
  (result 0 0 (signedBits 0 0) (signedBits 0 0)) == 0
#guard signedValue 4
  (result 0 4 (signedBits 0 0) (signedBits 4 (-7))) == 0
#guard signedValue 4
  (result 4 0 (signedBits 4 (-7)) (signedBits 0 0)) == 0

-- Representative asymmetric positive and negative products are exact.
#guard signedValue 7
  (result 4 3 (signedBits 4 (-3)) (signedBits 3 2)) == -6
#guard signedValue 8
  (result 3 5 (signedBits 3 3) (signedBits 5 (-7))) == -21

-- Minimum signed inputs are valid magnitudes and remain exact at the combined
-- width, including the minimum-times-minimum case.
#guard signedValue 7
  (result 4 3 (signedBits 4 (-8)) (signedBits 3 3)) == -24
#guard signedValue 7
  (result 4 3 (signedBits 4 (-8)) (signedBits 3 (-4))) == 32

example (leftWidth rightWidth : Nat)
    (left : Fin leftWidth → Bool) (right : Fin rightWidth → Bool) :
    resultValue leftWidth rightWidth left right =
      BitVector.ofBitVec
        (BitVec.ofInt (leftWidth + rightWidth)
          ((BitVector.toBitVec leftWidth left).toInt *
            (BitVector.toBitVec rightWidth right).toInt)) :=
  rfl

end SileanTests.SignedMultiplyContract
