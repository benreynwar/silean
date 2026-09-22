import HTFFT.Fixed.ButterflyCorrectness

namespace HTFFTTests.Butterfly

open HTFFT
open HTFFT.FixedPoint
open HTFFT.Butterfly

def initial : Fixed.Config := Fixed.Config.initial 4 2 4 2

def zero : Complex Int := ⟨0, 0⟩
def one : Complex Int := ⟨4, 0⟩

-- An exact grid-aligned butterfly: 1 ± (1 * 1).
#guard (Fixed.butterfly initial one one one).upper == (⟨8, 0⟩ : Complex Int)
#guard (Fixed.butterfly initial one one one).lower == zero

-- Width growth does not move the binary point.
#guard decodeComplex initial.outputFormat
  (Fixed.butterfly initial one one one).upper ==
    (⟨Rat.divInt 2 1, Rat.divInt 0 1⟩ : Complex Rat)

def roundingB : Complex Int := ⟨-4, -3⟩
def roundingTwiddle : Complex Int := ⟨-4, -2⟩

-- Each complex-product component is combined at full precision and then
-- rounded once using the selected ties-to-even policy.
#guard Fixed.multiply initial roundingB roundingTwiddle ==
  (⟨2, 5⟩ : Complex Int)

-- The mathematical contract is just the ordinary complex butterfly.
#guard (mathematical
  (⟨1, 0⟩ : Complex Int) (⟨2, 3⟩ : Complex Int)
  (⟨4, 5⟩ : Complex Int)).upper == ⟨-6, 22⟩
#guard (mathematical
  (⟨1, 0⟩ : Complex Int) (⟨2, 3⟩ : Complex Int)
  (⟨4, 5⟩ : Complex Int)).lower == ⟨8, -22⟩

-- The future accuracy theorem has a public, hardware-independent statement.
#check Fixed.HasLocalErrorBound
#check Fixed.hasLocalErrorBound
#check Fixed.butterfly_within_of_noOverflow
#check Fixed.butterfly_upper_error
#check Fixed.butterfly_lower_error

end HTFFTTests.Butterfly
