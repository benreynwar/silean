namespace Silean2.BitVector

/-! Arithmetic interpretation of fixed-width Boolean vectors. Bits are ordered
most-significant first. -/

@[reducible] def cardinality : Nat → Nat
  | 0 => 1
  | width + 1 => cardinality width + cardinality width

@[simp] theorem cardinality_eq_pow (width : Nat) : cardinality width = 2 ^ width := by
  induction width with
  | zero => rfl
  | succ width hypothesis =>
      simp [cardinality, hypothesis, Nat.pow_succ, Nat.mul_two]

def toNat : (width : Nat) → (Fin width → Bool) → Nat
  | 0, _ => 0
  | width + 1, bits =>
      (if bits 0 then cardinality width else 0) +
        toNat width (fun index => bits index.succ)

def toIndex : (width : Nat) → (Fin width → Bool) → Fin (cardinality width)
  | 0, _ => ⟨0, by simp [cardinality]⟩
  | width + 1, bits =>
      if bits 0 then
        Fin.natAdd (cardinality width) (toIndex width (fun index => bits index.succ))
      else
        Fin.castAdd (cardinality width) (toIndex width (fun index => bits index.succ))

@[simp] theorem toIndex_val : ∀ (width : Nat) (bits : Fin width → Bool),
    (toIndex width bits).val = toNat width bits
  | 0, _ => rfl
  | width + 1, bits => by
      cases head : bits 0 <;>
        simp [toIndex, toNat, head,
          toIndex_val width (fun index => bits index.succ), Fin.natAdd]

theorem toNat_lt_cardinality (width : Nat) (bits : Fin width → Bool) :
    toNat width bits < cardinality width := by
  rw [← toIndex_val]
  exact (toIndex width bits).isLt

end Silean2.BitVector
