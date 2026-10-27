namespace Silean2.Foundations

def bitVectorToNat {width : Nat} (bits : Vector Bool width) : Nat :=
  (List.finRange width).reverse.foldl (fun result i => result * 2 + bits[i].toNat) 0

def natToBitVector {width : Nat} (value : Fin (2 ^ width)) : Vector Bool width :=
  Vector.ofFn (fun i => value.val.testBit i.val)

def three : Vector Bool 3 := #v[true, true, false]

#guard bitVectorToNat three = 3

def collect
    {m : Type → Type} [Monad m]
    {n : Nat} {α : Fin n → Type}
    (f : (i : Fin n) → m (α i))
    : m ((i : Fin n) → α i) :=
  match n with
  | 0 => pure fun i => nomatch i
  | _ + 1 => do
    let head ← f 0
    let tail ← collect (fun i => f i.succ)
    return fun i =>
      match i with
      | ⟨0, _⟩ => head
      | ⟨k+1, _⟩ => tail ⟨ k, by omega⟩

def checkedFin (n i : Nat) : Except String (Fin n) :=
  if h : i < n then
    pure ⟨i, h⟩
  else
    throw s!"Index {i} is out of bounds for length {n}"

end Silean2.Foundations
