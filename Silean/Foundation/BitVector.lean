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

/-- Decode from the least-significant end: bit zero contributes one and the
remaining vector contributes twice its recursively decoded value. -/
theorem toNat_succ_low : ∀ (width : Nat) (bits : Fin (width + 1) → Bool),
    toNat (width + 1) bits =
      (bits 0).toNat + 2 * toNat width (fun index => bits index.succ)
  | 0, bits => by
      cases value : bits 0 <;> simp [toNat, cardinality, value]
  | width + 1, bits => by
      have lower := toNat_succ_low width
        (fun index : Fin (width + 1) => bits index.castSucc)
      cases high : bits (Fin.last (width + 1)) <;>
        cases low : bits 0 <;>
        simp [toNat, cardinality, high, low] at lower ⊢ <;>
        omega

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

theorem toNat_eq_zero_iff (width : Nat) (bits : Fin width → Bool) :
    toNat width bits = 0 ↔ ∀ index, bits index = false := by
  constructor
  · intro isZero
    have allFalse : bits = fun _ => false := by
      apply toNat_injective width
      simpa using isZero
    exact fun index => congrFun allFalse index
  · intro allFalse
    have bitsFalse : bits = fun _ => false := by
      funext index
      exact allFalse index
    simp [bitsFalse]

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

/-- Bits at and above the encoded width are zero. -/
@[simp] theorem testBit_toNat_of_width_le (width : Nat)
    (bits : Fin width → Bool) (index : Nat) (outside : width ≤ index) :
    (toNat width bits).testBit index = false := by
  apply Nat.testBit_lt_two_pow
  calc
    toNat width bits < cardinality width := toNat_lt_cardinality width bits
    _ = 2 ^ width := cardinality_eq_pow width
    _ ≤ 2 ^ index := Nat.pow_le_pow_right (by omega) outside

/-! ## Native `BitVec` bridge

Silean keeps hardware vectors in the uniform structural representation
`Fin width → element`; a bit vector is therefore `Fin width → Bool`. Native
`BitVec` remains the preferred packed representation for arithmetic that Lean
already provides. The conversions below are a proved boundary between those
roles rather than a second hardware-vector representation. -/

/-- Pack a Silean LSB-first Boolean vector into Lean's native `BitVec`. -/
def toBitVec (width : Nat) (bits : Fin width → Bool) : BitVec width :=
  BitVec.ofNat width (toNat width bits)

/-- Expose a native `BitVec` as Silean's LSB-first Boolean-vector
representation. -/
def ofBitVec {width : Nat} (bits : BitVec width) : Fin width → Bool :=
  bits.getLsb

/-- Packing preserves the unsigned natural-number interpretation. -/
@[simp] theorem toBitVec_toNat (width : Nat) (bits : Fin width → Bool) :
    (toBitVec width bits).toNat = toNat width bits := by
  rw [toBitVec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  simpa only [cardinality_eq_pow] using toNat_lt_cardinality width bits

/-- Packing preserves each individual bit. -/
@[simp] theorem getLsb_toBitVec (width : Nat) (bits : Fin width → Bool)
    (index : Fin width) :
    (toBitVec width bits).getLsb index = bits index := by
  change (toBitVec width bits).toNat.testBit index.val = bits index
  rw [toBitVec_toNat]
  exact testBit_toNat width bits index

/-- Packing Silean's low-bit encoding agrees with native `BitVec.ofNat`. -/
@[simp] theorem toBitVec_ofNat (width value : Nat) :
    toBitVec width (ofNat width value) = BitVec.ofNat width value := by
  apply BitVec.eq_of_toNat_eq
  simp only [toBitVec_toNat, toNat_ofNat, cardinality_eq_pow,
    BitVec.toNat_ofNat]

/-- Unpacking preserves the unsigned natural-number interpretation. -/
@[simp] theorem toNat_ofBitVec {width : Nat} (bits : BitVec width) :
    toNat width (ofBitVec bits) = bits.toNat := by
  have representation : ofBitVec bits = ofNat width bits.toNat := by
    funext index
    rfl
  rw [representation, toNat_ofNat, Nat.mod_eq_of_lt]
  simpa only [cardinality_eq_pow] using bits.isLt

/-- Unpacking a packed Silean vector recovers every bit. -/
@[simp] theorem ofBitVec_toBitVec (width : Nat) (bits : Fin width → Bool) :
    ofBitVec (toBitVec width bits) = bits := by
  funext index
  change (toBitVec width bits).toNat.testBit index.val = bits index
  rw [toBitVec_toNat]
  exact testBit_toNat width bits index

/-- Packing is injective because unpacking is its left inverse. -/
theorem toBitVec_injective (width : Nat) : Function.Injective (toBitVec width) := by
  intro left right equal
  rw [← ofBitVec_toBitVec width left, ← ofBitVec_toBitVec width right, equal]

/-- Packing an unpacked native vector recovers the native vector. -/
@[simp] theorem toBitVec_ofBitVec {width : Nat} (bits : BitVec width) :
    toBitVec width (ofBitVec bits) = bits := by
  apply BitVec.eq_of_toNat_eq
  rw [toBitVec_toNat, toNat_ofBitVec]

end Silean.BitVector
