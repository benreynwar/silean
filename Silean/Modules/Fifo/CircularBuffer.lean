namespace Silean.CircularBuffer

def distance (modulus read write : Nat) : Nat :=
  if read ≤ write then write - read else modulus - (read - write)

theorem distance_lt {modulus read write : Nat} (_modulusPositive : 0 < modulus)
    (readBound : read < modulus) (writeBound : write < modulus) :
    distance modulus read write < modulus := by
  unfold distance
  split <;> omega

theorem distance_eq_zero_iff {modulus read write : Nat}
    (_modulusPositive : 0 < modulus)
    (readBound : read < modulus) (_writeBound : write < modulus) :
    distance modulus read write = 0 ↔ read = write := by
  unfold distance
  split <;> omega

theorem distance_advance_write {modulus read write count : Nat}
    (_modulusPositive : 0 < modulus)
    (readBound : read < modulus) (writeBound : write < modulus)
    (countEq : distance modulus read write = count)
    (countBound : count + 1 < modulus) :
    distance modulus read ((write + 1) % modulus) = count + 1 := by
  by_cases noWrap : write + 1 < modulus
  · rw [Nat.mod_eq_of_lt noWrap]
    unfold distance at countEq ⊢
    split at countEq <;> split <;> omega
  · have wraps : write + 1 = modulus := by omega
    rw [wraps, Nat.mod_self]
    unfold distance at countEq ⊢
    split at countEq <;> split <;> omega

theorem distance_advance_read {modulus read write count : Nat}
    (_modulusPositive : 0 < modulus)
    (readBound : read < modulus) (writeBound : write < modulus)
    (countEq : distance modulus read write = count)
    (countPositive : 0 < count) :
    distance modulus ((read + 1) % modulus) write = count - 1 := by
  by_cases noWrap : read + 1 < modulus
  · rw [Nat.mod_eq_of_lt noWrap]
    unfold distance at countEq ⊢
    split at countEq <;> split <;> omega
  · have wraps : read + 1 = modulus := by omega
    rw [wraps, Nat.mod_self]
    unfold distance at countEq ⊢
    split at countEq <;> split <;> omega

theorem distance_advance_both {modulus read write : Nat}
    (_modulusPositive : 0 < modulus)
    (readBound : read < modulus) (writeBound : write < modulus) :
    distance modulus ((read + 1) % modulus) ((write + 1) % modulus) =
      distance modulus read write := by
  by_cases readNoWrap : read + 1 < modulus
  · rw [Nat.mod_eq_of_lt readNoWrap]
    by_cases writeNoWrap : write + 1 < modulus
    · rw [Nat.mod_eq_of_lt writeNoWrap]
      unfold distance
      split <;> split <;> omega
    · have writeWraps : write + 1 = modulus := by omega
      rw [writeWraps, Nat.mod_self]
      unfold distance
      split <;> split <;> omega
  · have readWraps : read + 1 = modulus := by omega
    rw [readWraps, Nat.mod_self]
    by_cases writeNoWrap : write + 1 < modulus
    · rw [Nat.mod_eq_of_lt writeNoWrap]
      unfold distance
      split <;> split <;> omega
    · have writeWraps : write + 1 = modulus := by omega
      rw [writeWraps, Nat.mod_self]
      unfold distance
      split <;> split <;> omega

section Indexed

variable (capacity : Nat) [NeZero capacity]

def advance (index : Fin capacity) (offset : Nat) : Fin capacity :=
  index + Fin.ofNat capacity offset

@[simp] theorem advance_zero (index : Fin capacity) :
    advance capacity index 0 = index := by
  apply Fin.ext
  simp [advance]

theorem advance_add (index : Fin capacity) (left right : Nat) :
    advance capacity (advance capacity index left) right =
      advance capacity index (left + right) := by
  apply Fin.ext
  simp only [advance, Fin.val_add, Fin.val_ofNat]
  simp [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

theorem advance_ofNat (value offset : Nat) :
    advance capacity (Fin.ofNat capacity value) offset =
      Fin.ofNat capacity (value + offset) := by
  apply Fin.ext
  simp [advance, Fin.val_add, Fin.val_ofNat, Nat.mod_add_mod,
    Nat.add_mod_mod]

theorem advance_distance_double (read write : Nat)
    (readBound : read < capacity + capacity)
    (writeBound : write < capacity + capacity) :
    advance capacity (Fin.ofNat capacity read)
        (distance (capacity + capacity) read write) =
      Fin.ofNat capacity write := by
  rw [advance_ofNat]
  unfold distance
  split
  · congr 1
    omega
  · apply Fin.ext
    simp only [Fin.val_ofNat]
    have capacityPositive : 0 < capacity := by
      have nonzero := NeZero.ne capacity
      omega
    have equation : read + ((capacity + capacity) - (read - write)) =
        write + capacity + capacity := by omega
    rw [equation]
    simp

theorem advance_ne_self {index : Fin capacity} {offset : Nat}
    (positive : 0 < offset) (below : offset < capacity) :
    advance capacity index offset ≠ index := by
  intro equal
  have values := Fin.ext_iff.mp equal
  simp only [advance, Fin.val_add] at values
  rw [Fin.val_ofNat] at values
  rw [Nat.mod_eq_of_lt below] at values
  by_cases noWrap : index.val + offset < capacity
  · rw [Nat.mod_eq_of_lt noWrap] at values
    omega
  · rw [Nat.mod_eq_sub_mod (by omega)] at values
    rw [Nat.mod_eq_of_lt (by omega)] at values
    omega

def values (entries : Fin capacity → α) :
    Fin capacity → Nat → List α
  | _, 0 => []
  | index, count + 1 =>
      entries index :: values entries (advance capacity index 1) count

@[simp] theorem values_zero (entries : Fin capacity → α)
    (index : Fin capacity) : values capacity entries index 0 = [] := rfl

@[simp] theorem values_succ (entries : Fin capacity → α)
    (index : Fin capacity) (count : Nat) :
    values capacity entries index (count + 1) =
      entries index :: values capacity entries (advance capacity index 1) count := rfl

@[simp] theorem values_length (entries : Fin capacity → α) :
    ∀ index count, (values capacity entries index count).length = count
  | _, 0 => rfl
  | index, count + 1 => by
      simp [values, values_length entries (advance capacity index 1) count]

theorem values_tail (entries : Fin capacity → α) (index : Fin capacity)
    (count : Nat) :
    (values capacity entries index count).tail =
      values capacity entries (advance capacity index 1) (count - 1) := by
  cases count <;> rfl

def write (entries : Fin capacity → α) (index : Fin capacity)
    (value : α) : Fin capacity → α :=
  fun other => if other = index then value else entries other

omit [NeZero capacity] in
@[simp] theorem write_selected (entries : Fin capacity → α)
    (index : Fin capacity) (value : α) :
    write capacity entries index value index = value := by
  simp [write]

omit [NeZero capacity] in
theorem write_other (entries : Fin capacity → α)
    (index : Fin capacity) (value : α) (other : Fin capacity)
    (different : other ≠ index) :
    write capacity entries index value other = entries other := by
  simp [write, different]

theorem values_write_tail (entries : Fin capacity → α)
    (start : Fin capacity) (value : α) :
    ∀ count, count < capacity →
      values capacity
        (write capacity entries (advance capacity start count) value)
        start (count + 1) =
      values capacity entries start count ++ [value]
  | 0, _ => by simp [values]
  | count + 1, below => by
      have headDifferent : start ≠ advance capacity start (count + 1) :=
        (advance_ne_self capacity (by omega) below).symm
      change write capacity entries (advance capacity start (count + 1)) value start ::
          values capacity
            (write capacity entries (advance capacity start (count + 1)) value)
            (advance capacity start 1) (count + 1) =
        (entries start :: values capacity entries (advance capacity start 1) count) ++
          [value]
      rw [write_other capacity entries _ value start headDifferent]
      rw [List.cons_append]
      congr 1
      have target : advance capacity start (count + 1) =
          advance capacity (advance capacity start 1) count := by
        rw [show count + 1 = 1 + count by omega]
        exact (advance_add capacity start 1 count).symm
      rw [target]
      exact values_write_tail entries (advance capacity start 1) value count (by omega)

theorem values_write_after_head (entries : Fin capacity → α)
    (start : Fin capacity) (value : α) (count : Nat)
    (positive : 0 < count) (below : count < capacity) :
    values capacity
        (write capacity entries (advance capacity start count) value)
        (advance capacity start 1) count =
      (values capacity entries start count).tail ++ [value] := by
  cases count with
  | zero => omega
  | succ count =>
      have whole := values_write_tail capacity entries start value (count + 1) below
      have headDifferent : start ≠ advance capacity start (count + 1) :=
        (advance_ne_self capacity (by omega) below).symm
      simp only [values_succ] at whole
      rw [write_other capacity entries _ value start headDifferent] at whole
      simp only [List.cons_append, List.cons.injEq] at whole
      simpa only [values_succ, List.tail_cons] using whole.2

end Indexed

end Silean.CircularBuffer
