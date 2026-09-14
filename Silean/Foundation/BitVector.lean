namespace Silean.BitVector

/-! Arithmetic interpretation of fixed-width Boolean vectors. Index `i` has
weight `2 ^ i`, so index zero is the least-significant bit. -/

@[reducible] def cardinality : Nat → Nat
  | 0 => 1
  | width + 1 => cardinality width + cardinality width

/-- The low `width` bits of a natural number, least-significant bit first. -/
def ofNat (width value : Nat) : Fin width → Bool :=
  fun index => value.testBit index.val

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

@[simp] theorem toNat_ofNat (width value : Nat) :
    toNat width (ofNat width value) = value % cardinality width := by
  rw [cardinality_eq_pow]
  induction width with
  | zero => simp [toNat, Nat.mod_one]
  | succ width induction =>
      change toNat width (fun index => value.testBit index.val) =
        value % 2 ^ width at induction
      rw [Nat.mod_pow_succ]
      cases bit : value.testBit width with
      | false =>
          have quotient : value / 2 ^ width % 2 = 0 := by
            rw [← Nat.toNat_testBit]
            simp [bit]
          simp [toNat, ofNat, induction, bit, quotient]
      | true =>
          have quotient : value / 2 ^ width % 2 = 1 := by
            rw [← Nat.toNat_testBit]
            simp [bit]
          simp [toNat, ofNat, induction, bit, quotient, Nat.add_comm]

/-- Reading a bit after interpreting a fixed-width vector as a natural number
recovers the original bit. -/
theorem testBit_toNat (width : Nat) (bits : Fin width → Bool)
    (index : Fin width) :
    (toNat width bits).testBit index.val = bits index := by
  have bound := toNat_lt_cardinality width bits
  rw [cardinality_eq_pow] at bound
  have recovered : ofNat width (toNat width bits) = bits := by
    apply toNat_injective width
    rw [toNat_ofNat, cardinality_eq_pow, Nat.mod_eq_of_lt bound]
  exact congrFun recovered index

end Silean.BitVector
