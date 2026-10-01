import HTFFT.Fixed.TwiddleTable
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

/-! # Precision-driven executable twiddle generation

All calculations in this file use exact rationals. The requested working
precision controls how many terms are retained; it is not an intermediate
fixed-width format. The only numerical loss is therefore the explicitly
bounded truncation of the arctangent and exponential series.
-/

namespace HTFFT.Fixed.TwiddleGenerator

open scoped BigOperators
open HTFFT HTFFT.FixedPoint

/-- First `terms` terms of the alternating arctangent series. -/
def atanSeries (x : Rat) (terms : Nat) : Rat :=
  ∑ term ∈ Finset.range terms,
    (-1 : Rat) ^ term * x ^ (2 * term + 1) / (2 * term + 1)

/-- Number of alternating-series pairs. Since Machin's largest argument is
`1/5`, each pair contributes more than four binary bits. -/
def arctangentIterations (workingBits : Nat) : Nat :=
  workingBits / 8 + 2

def arctangentTerms (workingBits : Nat) : Nat :=
  2 * arctangentIterations workingBits + 1

/-- Machin's formula evaluated with a precision-dependent number of exact
rational terms. The small arguments `1/5` and `1/239` make convergence much
faster than the requested binary precision. -/
def piApproximation (workingBits : Nat) : Rat :=
  let terms := arctangentTerms workingBits
  4 * (4 * atanSeries (1 / 5) terms - atanSeries (1 / 239) terms)

/-- A rational upper bound on the error in `piApproximation`. -/
def piError (workingBits : Nat) : Rat :=
  let last := arctangentTerms workingBits - 1
  4 * (4 * ((1 / 5 : Rat) ^ (2 * last + 1) / (2 * last + 1)) +
    (1 / 239 : Rat) ^ (2 * last + 1) / (2 * last + 1))

def rationalI : HTFFT.Complex Rat := ⟨0, 1⟩

/-- Written recursively so its embedding into Mathlib's complex numbers is
definitionally aligned with ordinary exponentiation. -/
def iPower : Nat → HTFFT.Complex Rat
  | 0 => ⟨1, 0⟩
  | power + 1 => iPower power * rationalI

def scale (factor : Rat) (value : HTFFT.Complex Rat) :
    HTFFT.Complex Rat :=
  ⟨factor * value.real, factor * value.imag⟩

/-- A finite complex-exponential series at the purely imaginary rational
argument `angle * I`. -/
def expSeries (angle : Rat) : Nat → HTFFT.Complex Rat
  | 0 => ⟨0, 0⟩
  | terms + 1 =>
      expSeries angle terms +
        scale (angle ^ terms / terms.factorial) (iPower terms)

/-- The series length used for a requested binary working precision. This is
deliberately generous: exact rational computation makes guard precision cheap,
and the proof treats the unused accuracy as margin. -/
def exponentialTerms (workingBits : Nat) : Nat :=
  workingBits + 13

/-- Uniform norm error budget before fixed-point quantization. The proof uses
five as a deliberately loose bound for the generated rational angle. -/
def approximationError (workingBits : Nat) : Rat :=
  let terms := exponentialTerms workingBits
  piError workingBits + 2 * 5 ^ terms / terms.factorial

/-- The exact rational accuracy requirement associated with a requested
binary working precision. It is executable, so concrete configurations can
discharge it with ordinary kernel reduction. -/
def PrecisionSufficient (workingBits : Nat) : Prop :=
  approximationError workingBits ≤ 1 / (2 : Rat) ^ workingBits

instance (workingBits : Nat) : Decidable (PrecisionSufficient workingBits) :=
  by
    unfold PrecisionSufficient
    infer_instance

/-- Rational angle used for a table entry. -/
def approximateAngle (workingBits : Nat) (stage : Fin depth)
    (offset : Fin (2 ^ stage.val)) : Rat :=
  -(piApproximation workingBits * offset.val / (2 ^ stage.val))

/-- Generate one rational twiddle from its stage and offset. -/
def value (workingBits : Nat) (stage : Fin depth)
    (offset : Fin (2 ^ stage.val)) : HTFFT.Complex Rat :=
  expSeries (approximateAngle workingBits stage offset)
    (exponentialTerms workingBits)

/-- Generate the complete approximation table. Every stage may request a
different working precision. -/
def approximations (depth : Nat) (workingBits : Fin depth → Nat) :
    RationalTwiddleTable depth where
  value stage := value (workingBits stage) stage

/-- Working precision selected from a destination format and an explicit
guard-bit budget. -/
def workingBits (formats : Fin depth → Format) (guardBits : Nat)
    (stage : Fin depth) : Nat :=
  (formats stage).fractionalBits + guardBits

/-- Generate approximations at the destination precision plus guard bits. -/
def forFormats (formats : Fin depth → Format) (guardBits : Nat) :
    RationalTwiddleTable depth :=
  approximations depth (workingBits formats guardBits)

theorem workingBits_gt_fractionalBits
    (formats : Fin depth → Format) {guardBits : Nat}
    (guardBits_pos : 0 < guardBits) (stage : Fin depth) :
    (formats stage).fractionalBits < workingBits formats guardBits stage := by
  simp [workingBits]
  omega

end HTFFT.Fixed.TwiddleGenerator
