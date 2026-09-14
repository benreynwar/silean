import Silean.Examples.PicoRV.Control
import Silean.Modules.Equality.Equality

namespace Silean.Examples.PicoRV.Control

open Silean

/-! Small semantic bridges between arithmetic predicates in the readable
Control contract and the bit-level comparisons used by its structure. -/

theorem signalTypeEqual_ofNat (width value : Nat)
    (bits : Fin width → Bool) (bound : value < 2 ^ width) :
    (SignalType.vector width .bit).equal bits (BitVector.ofNat width value) =
      decide (BitVector.toNat width bits = value) := by
  have encoded : BitVector.toNat width (BitVector.ofNat width value) = value := by
    rw [BitVector.toNat_ofNat, BitVector.cardinality_eq_pow,
      Nat.mod_eq_of_lt bound]
  by_cases matched : BitVector.toNat width bits = value
  · have bitsEqual : bits = BitVector.ofNat width value := by
      apply BitVector.toNat_injective width
      simpa [encoded] using matched
    have leftTrue : (SignalType.vector width .bit).equal bits
        (BitVector.ofNat width value) = true :=
      ((SignalType.vector width .bit).equal_eq_true_iff _ _).mpr bitsEqual
    have rightTrue : decide (BitVector.toNat width bits = value) = true := by
      simp [matched]
    rw [leftTrue, rightTrue]
  · have bitsDifferent : bits ≠ BitVector.ofNat width value := by
      intro equal
      apply matched
      rw [equal, encoded]
    have rightFalse : decide (BitVector.toNat width bits = value) = false := by
      simp [matched]
    rw [rightFalse]
    cases left : (SignalType.vector width .bit).equal bits
        (BitVector.ofNat width value)
    · rfl
    · have equal :=
        ((SignalType.vector width .bit).equal_eq_true_iff _ _).mp left
      exact (bitsDifferent equal).elim

theorem word_mod_four_ne_zero (bits : Fin 32 → Bool) :
    decide (BitVector.toNat 32 bits % 4 ≠ 0) = (bits 0 || bits 1) := by
  let value := BitVector.toNat 32 bits
  have bit0 := BitVector.testBit_toNat 32 bits (0 : Fin 32)
  have bit1 := BitVector.testBit_toNat 32 bits (1 : Fin 32)
  change value.testBit 0 = bits 0 at bit0
  change value.testBit 1 = bits 1 at bit1
  rw [Nat.testBit_zero] at bit0
  rw [Nat.testBit_succ, Nat.testBit_zero] at bit1
  have lowBound : value % 2 < 2 := Nat.mod_lt _ (by decide)
  have nextBound : value / 2 % 2 < 2 := Nat.mod_lt _ (by decide)
  have decompose : value % 4 =
      value % 2 + 2 * (value / 2 % 2) := by
    simpa using (Nat.mod_pow_succ (x := value) (b := 2) (k := 1))
  cases low : bits 0 <;> cases high : bits 1 <;>
    simp [low, high] at bit0 bit1 ⊢ <;> omega

end Silean.Examples.PicoRV.Control
