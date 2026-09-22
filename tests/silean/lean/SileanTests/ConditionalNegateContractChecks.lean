import Silean.Modules.ConditionalNegate.ConditionalNegate

namespace SileanTests.ConditionalNegateContract

open Silean
open Silean.Modules.ConditionalNegate

def bits (width value : Nat) : Fin width → Bool :=
  BitVector.ofNat width value

def inputs (width : Nat) (value : Fin width → Bool) (negate : Bool) :
    (ports width).inputs.Values
  | .value => value
  | .negate => negate

def result (width : Nat) (value : Fin width → Bool) (negate : Bool) :=
  ((cycleContract width).evaluate
    (inputs width value negate) SignalMap.emptyValues).1 .result

def signedValue (width : Nat) (value : Fin width → Bool) : Int :=
  (BitVector.toBitVec width value).toInt

-- Width zero has one value and remains well defined in both modes.
#guard signedValue 0 (result 0 (bits 0 0) false) == 0
#guard signedValue 0 (result 0 (bits 0 0) true) == 0

-- Ordinary values are preserved or negated according to the control.
#guard signedValue 4 (result 4 (bits 4 3) false) == 3
#guard signedValue 4 (result 4 (bits 4 3) true) == -3

-- The most-negative two's-complement value negates to itself at fixed width.
#guard signedValue 4 (bits 4 8) == -8
#guard signedValue 4 (result 4 (bits 4 8) true) == -8

example (width : Nat) {step : (cycleContract width).Step}
    (allowed : (cycleContract width).Allows step) :
    BitVector.toBitVec width (step.outputs .result) =
      bif step.inputs .negate then
        -BitVector.toBitVec width (step.inputs .value)
      else
        BitVector.toBitVec width (step.inputs .value) :=
  result_toBitVec_of_allowed width allowed

end SileanTests.ConditionalNegateContract
