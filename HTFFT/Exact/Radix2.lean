import HTFFT.Exact.Indexing
import Mathlib.Analysis.Fourier.ZMod

namespace HTFFT.Exact

/-- The canonical change of index representation used at the Mathlib DFT
boundary. Its inverse chooses the standard representative in
`Fin (2 ^ depth)`. -/
def zmodIndexEquiv (depth : Nat) : Fin (2 ^ depth) ≃ ZMod (2 ^ depth) :=
  ZMod.finEquiv (2 ^ depth)

/-- The exact forward-transform twiddle `exp (-2 * pi * I * k / 2^depth)`.
Writing it with `ZMod.stdAddChar` fixes the same negative-exponent convention
used by Mathlib's unnormalized `ZMod.dft`. -/
noncomputable def twiddle (depth : Nat) (k : Fin (2 ^ depth)) : ℂ :=
  ZMod.stdAddChar (-(zmodIndexEquiv depth k))

@[simp]
theorem twiddle_zero (depth : Nat) : twiddle depth 0 = 1 := by
  simp [twiddle, zmodIndexEquiv]

/-- The exact recursive decimation-in-time radix-two FFT. Inputs are split by
parity. For each `k`, the sum is placed at output `k` and the difference at
output `k + 2^depth`, giving natural-frequency-order output. -/
noncomputable def radix2 : (depth : Nat) → Vector depth ℂ → Vector depth ℂ
  | 0, input => input
  | depth + 1, input =>
      let evenTransform := radix2 depth (evens input)
      let oddTransform := radix2 depth (odds input)
      concatHalves
        (fun k => evenTransform k +
          twiddle (depth + 1) (halfIndexEquiv depth (Sum.inl k)) * oddTransform k)
        (fun k => evenTransform k -
          twiddle (depth + 1) (halfIndexEquiv depth (Sum.inl k)) * oddTransform k)

@[simp]
theorem radix2_firstHalf (input : Vector (depth + 1) ℂ)
    (k : Fin (2 ^ depth)) :
    radix2 (depth + 1) input (halfIndexEquiv depth (Sum.inl k)) =
      radix2 depth (evens input) k +
        twiddle (depth + 1) (halfIndexEquiv depth (Sum.inl k)) *
          radix2 depth (odds input) k := by
  rw [radix2, concatHalves_first]

@[simp]
theorem radix2_secondHalf (input : Vector (depth + 1) ℂ)
    (k : Fin (2 ^ depth)) :
    radix2 (depth + 1) input (halfIndexEquiv depth (Sum.inr k)) =
      radix2 depth (evens input) k -
        twiddle (depth + 1) (halfIndexEquiv depth (Sum.inl k)) *
          radix2 depth (odds input) k := by
  rw [radix2, concatHalves_second]

/-- Change only the finite index representation at the Mathlib DFT boundary. -/
def toZModVector (input : Vector depth α) : ZMod (2 ^ depth) → α :=
  input ∘ (zmodIndexEquiv depth).symm

/-- The pointwise theorem to be proved after the one-step Cooley--Tukey
identity is available. This deliberately refers directly to `ZMod.dft`; there
is no second project-local definition of the DFT. -/
def Radix2AgreesWithDFT : Prop :=
  ∀ (depth : Nat) (input : Vector depth ℂ) (k : Fin (2 ^ depth)),
    radix2 depth input k =
      ZMod.dft (toZModVector input) (zmodIndexEquiv depth k)

end HTFFT.Exact
