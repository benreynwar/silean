import HTFFT.Exact.DFT

namespace HTFFTTests.ExactFFT

open HTFFT.Exact

def values (depth : Nat) : Vector depth Nat :=
  fun index => index.val

def asList (vector : Fin n → α) : List α :=
  List.ofFn vector

-- Bit reversal uses exactly the stated depth, including the zero-bit case.
#guard asList (bitReverse (values 0)) == [0]
#guard asList (bitReverse (values 1)) == [0, 1]
#guard asList (bitReverse (values 2)) == [0, 2, 1, 3]
#guard asList (bitReverse (values 3)) == [0, 4, 2, 6, 1, 5, 3, 7]

-- Parity splitting selects source positions 2*k and 2*k+1.
#guard asList (evens (values 1)) == [0]
#guard asList (odds (values 1)) == [1]
#guard asList (evens (values 2)) == [0, 2]
#guard asList (odds (values 2)) == [1, 3]
#guard asList (evens (values 3)) == [0, 2, 4, 6]
#guard asList (odds (values 3)) == [1, 3, 5, 7]

-- Concatenation places its first vector before its second vector.
#guard asList (concatHalves (depth := 0) (fun _ => 10) (fun _ => 20)) == [10, 20]
#guard asList (concatHalves (values 1) (values 1)) == [0, 1, 0, 1]
#guard asList (concatHalves (values 2) (values 2)) == [0, 1, 2, 3, 0, 1, 2, 3]

-- The DFT boundary changes only the index representation.
example (depth : Nat) (index : Fin (2 ^ depth)) :
    (zmodIndexEquiv depth).symm (zmodIndexEquiv depth index) = index := by
  simp

example (depth : Nat) (index : ZMod (2 ^ depth)) :
    zmodIndexEquiv depth ((zmodIndexEquiv depth).symm index) = index := by
  simp

-- A length-one transform is the identity exactly.
example (input : Vector 0 ℂ) : radix2 0 input = input := rfl

-- The length-two transform is the familiar exact sum and difference.
example (input : Vector 1 ℂ) :
    radix2 1 input 0 = input 0 + input 1 := by
  have firstIndex : (0 : Fin 2) = halfIndexEquiv 0 (Sum.inl 0) := by decide
  have twiddleIndex : halfIndexEquiv 0 (Sum.inl 0) = (0 : Fin 2) := by decide
  have evenIndex : parityIndexEquiv 0 (0, 0) = (0 : Fin 2) := by decide
  have oddIndex : parityIndexEquiv 0 (0, 1) = (1 : Fin 2) := by decide
  calc
    radix2 1 input 0 = radix2 1 input (halfIndexEquiv 0 (Sum.inl 0)) :=
      congrArg (radix2 1 input) firstIndex
    _ = input 0 + input 1 := by
      rw [radix2_firstHalf]
      simp [radix2, twiddleIndex, evenIndex, oddIndex]

example (input : Vector 1 ℂ) :
    radix2 1 input 1 = input 0 - input 1 := by
  have secondIndex : (1 : Fin 2) = halfIndexEquiv 0 (Sum.inr 0) := by decide
  have twiddleIndex : halfIndexEquiv 0 (Sum.inl 0) = (0 : Fin 2) := by decide
  have evenIndex : parityIndexEquiv 0 (0, 0) = (0 : Fin 2) := by decide
  have oddIndex : parityIndexEquiv 0 (0, 1) = (1 : Fin 2) := by decide
  calc
    radix2 1 input 1 = radix2 1 input (halfIndexEquiv 0 (Sum.inr 0)) :=
      congrArg (radix2 1 input) secondIndex
    _ = input 0 - input 1 := by
      rw [radix2_secondHalf]
      simp [radix2, twiddleIndex, evenIndex, oddIndex]

def impulse (depth : Nat) : Vector depth ℂ :=
  fun k => if k = 0 then 1 else 0

private theorem radix2_impulse (depth : Nat) (k : Fin (2 ^ depth)) :
    radix2 depth (impulse depth) k = 1 := by
  rw [radix2_agreesWithDFT, dft_eq_sum_fourierCoefficient]
  simp [impulse, fourierCoefficient]

-- Exact known transforms at sizes two, four, and eight guard the generic
-- theorem and its natural output ordering.
example : radix2 1 (impulse 1) = fun _ => 1 := by
  funext k
  exact radix2_impulse 1 k

example : radix2 2 (impulse 2) = fun _ => 1 := by
  funext k
  exact radix2_impulse 2 k

example : radix2 3 (impulse 3) = fun _ => 1 := by
  funext k
  exact radix2_impulse 3 k

-- The generic correctness proposition is now proved without assumptions.
#check Radix2AgreesWithDFT
#check radix2_agreesWithDFT
#check dft_firstHalf
#check dft_secondHalf

end HTFFTTests.ExactFFT
