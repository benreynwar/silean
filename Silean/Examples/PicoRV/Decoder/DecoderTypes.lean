import Silean.Foundation.BitVector

namespace Silean.Examples.PicoRV.Decoder

open Silean

abbrev Word := Fin 32 → Bool
abbrev RegisterAddress := Fin 5 → Bool

def wordOfNat (value : Nat) : Word := fun index => value.testBit index.val

def addressOfNat (value : Nat) : RegisterAddress :=
  fun index => value.testBit index.val

def field (word : Word) (low width : Nat) : Nat :=
  (BitVector.toNat 32 word / 2 ^ low) % 2 ^ width

def opcode (word : Word) : Nat := field word 0 7
def funct3 (word : Word) : Nat := field word 12 3
def funct7 (word : Word) : Nat := field word 25 7

def signExtend (width : Nat) (value : Nat) : Word :=
  let modulus := 2 ^ width
  let extended := if value < 2 ^ (width - 1) then value else value + 2 ^ 32 - modulus
  wordOfNat extended

def immediateJ (word : Word) : Word :=
  signExtend 21
    (field word 21 10 * 2 + field word 20 1 * 2 ^ 11 +
      field word 12 8 * 2 ^ 12 + field word 31 1 * 2 ^ 20)

def immediateI (word : Word) : Word := signExtend 12 (field word 20 12)

def immediateB (word : Word) : Word :=
  signExtend 13
    (field word 8 4 * 2 + field word 25 6 * 2 ^ 5 +
      field word 7 1 * 2 ^ 11 + field word 31 1 * 2 ^ 12)

def immediateS (word : Word) : Word :=
  signExtend 12 (field word 7 5 + field word 25 7 * 2 ^ 5)

def immediateU (word : Word) : Word := wordOfNat (field word 12 20 * 2 ^ 12)

def boolOr (values : List Bool) : Bool := values.any id

end Silean.Examples.PicoRV.Decoder
