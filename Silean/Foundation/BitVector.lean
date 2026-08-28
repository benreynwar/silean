namespace Silean.BitVector

/-! Arithmetic interpretation of fixed-width Boolean vectors. Index `i` has
weight `2 ^ i`, so index zero is the least-significant bit. -/

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
      (if bits (Fin.last width) then cardinality width else 0) +
        toNat width (fun index => bits index.castSucc)

def toIndex : (width : Nat) → (Fin width → Bool) → Fin (cardinality width)
  | 0, _ => ⟨0, by simp [cardinality]⟩
  | width + 1, bits =>
      if bits (Fin.last width) then
        Fin.natAdd (cardinality width) (toIndex width (fun index => bits index.castSucc))
      else
        Fin.castAdd (cardinality width) (toIndex width (fun index => bits index.castSucc))

@[simp] theorem toNat_false : ∀ width : Nat,
    toNat width (fun _ => false) = 0
  | 0 => rfl
  | width + 1 => by simp [toNat, toNat_false width]

@[simp] theorem toIndex_val : ∀ (width : Nat) (bits : Fin width → Bool),
    (toIndex width bits).val = toNat width bits
  | 0, _ => rfl
  | width + 1, bits => by
      cases high : bits (Fin.last width) <;>
        simp [toIndex, toNat, high,
          toIndex_val width (fun index => bits index.castSucc), Fin.natAdd]

theorem toNat_lt_cardinality (width : Nat) (bits : Fin width → Bool) :
    toNat width bits < cardinality width := by
  rw [← toIndex_val]
  exact (toIndex width bits).isLt

theorem toNat_injective (width : Nat) : Function.Injective (toNat width) := by
  induction width with
  | zero =>
      intro left right _
      funext index
      exact Fin.elim0 index
  | succ width induction =>
      intro left right equal
      have leftBound := toNat_lt_cardinality width (fun index => left index.castSucc)
      have rightBound := toNat_lt_cardinality width (fun index => right index.castSucc)
      simp only [cardinality_eq_pow] at leftBound rightBound
      have highEqual : left (Fin.last width) = right (Fin.last width) := by
        cases leftHigh : left (Fin.last width) <;>
          cases rightHigh : right (Fin.last width) <;>
          simp [toNat, leftHigh, rightHigh] at equal ⊢ <;> omega
      have lowerEqual : (fun index : Fin width => left index.castSucc) =
          (fun index : Fin width => right index.castSucc) := by
        apply induction
        cases leftHigh : left (Fin.last width) <;>
          cases rightHigh : right (Fin.last width) <;>
          simp [toNat, leftHigh, rightHigh] at equal ⊢ <;> omega
      funext index
      refine Fin.lastCases ?_ (fun lower => ?_) index
      · exact highEqual
      · exact congrFun lowerEqual lower

end Silean.BitVector
