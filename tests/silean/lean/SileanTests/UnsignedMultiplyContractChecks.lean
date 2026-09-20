import Silean.Modules.UnsignedMultiply.UnsignedMultiply

namespace SileanTests.UnsignedMultiplyContract

open Silean
open Silean.Modules.UnsignedMultiply

def bits (width value : Nat) : Fin width → Bool :=
  BitVector.ofNat width value

def inputs (leftWidth rightWidth : Nat)
    (left : Fin leftWidth → Bool) (right : Fin rightWidth → Bool) :
    (ports leftWidth rightWidth).inputs.Values
  | .left => left
  | .right => right

def result (leftWidth rightWidth : Nat)
    (left : Fin leftWidth → Bool) (right : Fin rightWidth → Bool) :=
  ((cycleContract leftWidth rightWidth).evaluate
    (inputs leftWidth rightWidth left right) SignalMap.emptyValues).1 .result

-- 1011 × 101 = 0110111 at the full seven-bit result width.
#guard BitVector.toNat 7 (result 4 3 (bits 4 11) (bits 3 5)) == 55

-- A zero-width operand denotes zero. The other operand still determines the
-- result width, and every result bit is zero.
#guard BitVector.toNat 4 (result 0 4 (bits 0 0) (bits 4 13)) == 0
#guard BitVector.toNat 4 (result 4 0 (bits 4 13) (bits 0 0)) == 0
#guard BitVector.toNat 0 (result 0 0 (bits 0 0) (bits 0 0)) == 0

example (leftWidth rightWidth : Nat)
    (left : Fin leftWidth → Bool) (right : Fin rightWidth → Bool) :
    BitVector.toNat (leftWidth + rightWidth)
        (resultValue leftWidth rightWidth left right) =
      BitVector.toNat leftWidth left * BitVector.toNat rightWidth right := by
  exact toNat_resultValue leftWidth rightWidth left right

example (rightWidth : Nat) (right : Fin rightWidth → Bool) :
    resultValue 0 rightWidth (bits 0 0) right =
      BitVector.ofNat (0 + rightWidth) 0 := by
  simp

example (leftWidth : Nat) (left : Fin leftWidth → Bool) :
    resultValue leftWidth 0 left (bits 0 0) = BitVector.ofNat leftWidth 0 := by
  simp

example (leftWidth rightWidth : Nat)
    {step : (cycleContract leftWidth rightWidth).Step}
    (allowed : (cycleContract leftWidth rightWidth).Allows step) :
    BitVector.toNat (leftWidth + rightWidth) (step.outputs .result) =
      BitVector.toNat leftWidth (step.inputs .left) *
        BitVector.toNat rightWidth (step.inputs .right) :=
  result_toNat_of_allowed leftWidth rightWidth allowed

end SileanTests.UnsignedMultiplyContract
