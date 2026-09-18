import PicoRV.Control
import Silean.Modules.Equality.Equality

namespace PicoRV.Control

open Silean

/-! Small semantic bridges between arithmetic predicates in the readable
Control contract and the bit-level comparisons used by its structure. -/

theorem signalTypeEqual_ofNat (width value : Nat)
    (bits : Fin width → Bool) (bound : value < 2 ^ width) :
    (Silean.SignalType.vector width .bit).equal bits (Silean.BitVector.ofNat width value) =
      decide (Silean.BitVector.toNat width bits = value) := by
  have encoded : Silean.BitVector.toNat width (Silean.BitVector.ofNat width value) = value := by
    rw [Silean.BitVector.toNat_ofNat, Silean.BitVector.cardinality_eq_pow,
      Nat.mod_eq_of_lt bound]
  by_cases matched : Silean.BitVector.toNat width bits = value
  · have bitsEqual : bits = Silean.BitVector.ofNat width value := by
      apply Silean.BitVector.toNat_injective width
      simpa [encoded] using matched
    have leftTrue : (Silean.SignalType.vector width .bit).equal bits
        (Silean.BitVector.ofNat width value) = true :=
      ((Silean.SignalType.vector width .bit).equal_eq_true_iff _ _).mpr bitsEqual
    have rightTrue : decide (Silean.BitVector.toNat width bits = value) = true := by
      simp [matched]
    rw [leftTrue, rightTrue]
  · have bitsDifferent : bits ≠ Silean.BitVector.ofNat width value := by
      intro equal
      apply matched
      rw [equal, encoded]
    have rightFalse : decide (Silean.BitVector.toNat width bits = value) = false := by
      simp [matched]
    rw [rightFalse]
    cases left : (Silean.SignalType.vector width .bit).equal bits
        (Silean.BitVector.ofNat width value)
    · rfl
    · have equal :=
        ((Silean.SignalType.vector width .bit).equal_eq_true_iff _ _).mp left
      exact (bitsDifferent equal).elim

theorem word_mod_four_ne_zero (bits : Fin 32 → Bool) :
    decide (Silean.BitVector.toNat 32 bits % 4 ≠ 0) = (bits 0 || bits 1) := by
  let value := Silean.BitVector.toNat 32 bits
  have bit0 := Silean.BitVector.testBit_toNat 32 bits (0 : Fin 32)
  have bit1 := Silean.BitVector.testBit_toNat 32 bits (1 : Fin 32)
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

end PicoRV.Control
