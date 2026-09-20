import Silean.Modules.CarrySaveTree.CarrySaveTree

namespace SileanTests.CarrySaveTreeContract

open Silean
open Silean.Modules.CarrySaveTree

def bits (width value : Nat) : Fin width → Bool :=
  BitVector.ofNat width value

def noOperands (width : Nat) : Fin 0 → Fin width → Bool :=
  fun index => Fin.elim0 index

def oneOperand (width value : Nat) : Fin 1 → Fin width → Bool :=
  fun _ => bits width value

def twoOperands (width first second : Nat) : Fin 2 → Fin width → Bool
  | 0 => bits width first
  | 1 => bits width second

def threeOperands (width first second third : Nat) : Fin 3 → Fin width → Bool
  | 0 => bits width first
  | 1 => bits width second
  | 2 => bits width third

def inputs (width operandCount : Nat)
    (operands : Fin operandCount → Fin width → Bool) :
    (ports width operandCount).inputs.Values
  | .operands => operands

def outputs (width operandCount : Nat)
    (resultA resultB : Fin width → Bool) :
    (ports width operandCount).outputs.Values
  | .resultA => resultA
  | .resultB => resultB

-- Empty, singleton, and pair collections use their natural representations.
example : Accepts 4 0 (noOperands 4) (bits 4 0) (bits 4 0) := by
  rw [accepts_zero_iff]
  exact ⟨rfl, rfl⟩

example : Accepts 4 1 (oneOperand 4 11) (bits 4 11) (bits 4 0) := by
  rw [accepts_one_iff]
  exact ⟨rfl, rfl⟩

example : Accepts 4 2 (twoOperands 4 5 9) (bits 4 5) (bits 4 9) := by
  rw [accepts_two_iff]
  exact ⟨rfl, rfl⟩

-- Larger collections constrain the total but not the particular output pair.
example : Accepts 4 3 (threeOperands 4 9 6 7) (bits 4 8) (bits 4 14) := by
  constructor
  · simp only [PreservesTotal]
    native_decide
  · trivial

example : Accepts 4 3 (threeOperands 4 9 6 7) (bits 4 0) (bits 4 6) := by
  constructor
  · simp only [PreservesTotal]
    native_decide
  · trivial

example : ¬Accepts 4 3 (threeOperands 4 9 6 7) (bits 4 0) (bits 4 5) := by
  intro accepted
  have notPreserved :
      ¬PreservesTotal 4 3 (threeOperands 4 9 6 7) (bits 4 0) (bits 4 5) := by
    simp only [PreservesTotal]
    native_decide
  exact notPreserved accepted.1

-- The custom contract relates the values at the actual module boundary.
example : contract 4 3 (inputs 4 3 (threeOperands 4 9 6 7))
    (outputs 4 3 (bits 4 8) (bits 4 14)) := by
  change Accepts 4 3 (threeOperands 4 9 6 7) (bits 4 8) (bits 4 14)
  constructor
  · simp only [PreservesTotal]
    native_decide
  · trivial

example (width operandCount : Nat)
    (operands : Fin operandCount → Fin width → Bool)
    (resultA resultB : Fin width → Bool)
    (accepted : Accepts width operandCount operands resultA resultB) :
    (BitVector.toNat width resultA + BitVector.toNat width resultB) %
        BitVector.cardinality width =
      inputTotal width operandCount operands % BitVector.cardinality width := by
  exact preservesTotal_of_accepts width operandCount accepted

end SileanTests.CarrySaveTreeContract
