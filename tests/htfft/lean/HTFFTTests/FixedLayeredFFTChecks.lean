import HTFFT.Fixed.LayeredCorrectness

namespace HTFFTTests.FixedLayeredFFT

open HTFFT
open HTFFT.Fixed

def config2 : Config 2 := Config.initial 2 8 2 4 2

def unityTable2 : TwiddleTable 2 where
  value _ _ := ⟨4, 0⟩

def input2 : Vector 2
  | ⟨0, _⟩ => ⟨4, 0⟩
  | ⟨1, _⟩ => ⟨8, 0⟩
  | ⟨2, _⟩ => ⟨12, 0⟩
  | _ => ⟨16, 0⟩

-- Boundary formats grow one signed component bit without moving the binary
-- point.
#guard (config2.boundaryFormat 0).width == 8
#guard (config2.boundaryFormat (Fin.last 2)).width == 10
#guard (config2.boundaryFormat (Fin.last 2)).fractionalBits == 2

-- Prefix zero is exactly the shared bit-reversal operation.
#guard layeredPrefix config2 unityTable2 0 input2 == Exact.bitReverse input2

-- With unity in every table slot this executable two-layer example exercises
-- the shared indexing and stage-dependent format transitions.
#guard layeredFFT config2 unityTable2 input2 ==
  (fun
    | ⟨0, _⟩ => ⟨40, 0⟩
    | ⟨1, _⟩ => ⟨-16, 0⟩
    | ⟨2, _⟩ => ⟨-8, 0⟩
    | _ => ⟨0, 0⟩)

#check TwiddleAccuracy
#check NoOverflow
#check boundsAt
#check boundsAt_magnitude
#check boundsAt_error_of_exactTwiddles
#check layeredSuffix
#check butterflyLayer_magnitudeBound
#check butterflyLayer_within
#check layeredPrefix_bounds
#check layeredFFT_within
#check layeredFFT_within_decodedInput
#check layeredFFT_within_quantizedInput
#check layeredFFT_within_encodedInput
#check layeredFFT_pointwise_dft
#check layeredFFT_fits

end HTFFTTests.FixedLayeredFFT
