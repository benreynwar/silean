import Mathlib.Data.BitVec
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic

open scoped BigOperators

namespace HTFFT.Exact

/-- A vector whose length is determined by its radix-two depth. -/
abbrev Vector (depth : Nat) (α : Type) := Fin (2 ^ depth) → α

/-- Interpret a half-size index together with a parity bit as an index into the
next larger vector. The parity bit is the low bit, so `0` selects an even input
and `1` selects an odd input. -/
def parityIndexEquiv (depth : Nat) :
    Fin (2 ^ depth) × Fin 2 ≃ Fin (2 ^ (depth + 1)) :=
  finProdFinEquiv.trans (finCongr (by simp [Nat.pow_succ]))

@[simp]
theorem parityIndexEquiv_val (depth : Nat) (index : Fin (2 ^ depth))
    (parity : Fin 2) :
    (parityIndexEquiv depth (index, parity)).val =
      parity.val + 2 * index.val :=
  rfl

/-- The even-indexed half of a vector. -/
def evens (input : Vector (depth + 1) α) : Vector depth α :=
  fun index => input (parityIndexEquiv depth (index, 0))

@[simp]
theorem evens_apply (input : Vector (depth + 1) α) (index : Fin (2 ^ depth)) :
    evens input index = input (parityIndexEquiv depth (index, 0)) :=
  rfl

/-- The odd-indexed half of a vector. -/
def odds (input : Vector (depth + 1) α) : Vector depth α :=
  fun index => input (parityIndexEquiv depth (index, 1))

@[simp]
theorem odds_apply (input : Vector (depth + 1) α) (index : Fin (2 ^ depth)) :
    odds input index = input (parityIndexEquiv depth (index, 1)) :=
  rfl

/-- Interpret a choice of the first or second half as an index into the next
larger vector. `Sum.inl k` denotes `k`; `Sum.inr k` denotes `k + 2^depth`. -/
def halfIndexEquiv (depth : Nat) :
    Fin (2 ^ depth) ⊕ Fin (2 ^ depth) ≃ Fin (2 ^ (depth + 1)) :=
  finSumFinEquiv.trans (finCongr (by simp [Nat.pow_succ, Nat.mul_two]))

@[simp]
theorem halfIndexEquiv_left_val (depth : Nat) (index : Fin (2 ^ depth)) :
    (halfIndexEquiv depth (Sum.inl index)).val = index.val :=
  rfl

@[simp]
theorem halfIndexEquiv_right_val (depth : Nat) (index : Fin (2 ^ depth)) :
    (halfIndexEquiv depth (Sum.inr index)).val = 2 ^ depth + index.val :=
  rfl

/-- Concatenate two equal-sized vectors. The first argument occupies the
lower-numbered half and the second occupies the upper-numbered half. -/
def concatHalves (first second : Vector depth α) : Vector (depth + 1) α :=
  fun index =>
    match (halfIndexEquiv depth).symm index with
    | Sum.inl k => first k
    | Sum.inr k => second k

@[simp]
theorem concatHalves_first (first second : Vector depth α)
    (index : Fin (2 ^ depth)) :
    concatHalves first second (halfIndexEquiv depth (Sum.inl index)) = first index := by
  simp [concatHalves]

@[simp]
theorem concatHalves_second (first second : Vector depth α)
    (index : Fin (2 ^ depth)) :
    concatHalves first second (halfIndexEquiv depth (Sum.inr index)) = second index := by
  simp [concatHalves]

/-- Reindex a sum over a radix-two vector into its even and odd entries. -/
theorem sum_parity [AddCommMonoid β] (depth : Nat)
    (f : Fin (2 ^ (depth + 1)) → β) :
    ∑ i, f i = ∑ j : Fin (2 ^ depth),
      (f (parityIndexEquiv depth (j, 0)) +
        f (parityIndexEquiv depth (j, 1))) := by
  calc
    ∑ i, f i = ∑ p : Fin (2 ^ depth) × Fin 2,
        f (parityIndexEquiv depth p) :=
      ((parityIndexEquiv depth).sum_comp f).symm
    _ = ∑ j : Fin (2 ^ depth), ∑ p : Fin 2,
        f (parityIndexEquiv depth (j, p)) :=
      Fintype.sum_prod_type _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Fin.sum_univ_two]

/-- Reverse exactly `depth` index bits. -/
def bitReverseIndex (index : Fin (2 ^ depth)) : Fin (2 ^ depth) :=
  (BitVec.ofFin index).reverse.toFin

@[simp]
theorem bitReverseIndex_involutive : Function.Involutive (@bitReverseIndex depth) := by
  intro index
  simp [bitReverseIndex, BitVec.reverse_reverse_eq]

/-- Reorder a vector by reversing the bits of each destination index. Since
bit reversal is an involution, this is also the corresponding source-index
permutation. -/
def bitReverse (input : Vector depth α) : Vector depth α :=
  fun index => input (bitReverseIndex index)

@[simp]
theorem bitReverse_involutive : Function.Involutive (@bitReverse depth α) := by
  intro input
  funext index
  simp only [bitReverse]
  rw [bitReverseIndex_involutive index]

end HTFFT.Exact
