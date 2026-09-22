import HTFFT.Silean.PipelinedSignedComplexMultiply.PipelinedSignedComplexMultiply

assert_not_imported HTFFT.Silean.PipelinedSignedComplexMultiply.Internal.PipelinedSignedComplexMultiplyStructure
assert_not_imported HTFFT.Silean.PipelinedSignedComplexMultiply.Internal.PipelinedSignedComplexMultiplyVerification

namespace HTFFTTests.PipelinedSignedComplexMultiplyContract

open _root_.Silean
open HTFFT.Silean.PipelinedSignedComplexMultiply

def signedBits (width : Nat) (value : Int) : Fin width → Bool :=
  BitVector.ofBitVec (BitVec.ofInt width value)

-- The standalone public contract is phrased only as signed integer complex
-- multiplication, one rounding operation, and trace latency.
example :
    realNumerator 4 3
      (signedBits 4 3) (signedBits 4 1)
      (signedBits 3 2) (signedBits 3 (-1)) = 7 := by decide

example :
    imagNumerator 4 3
      (signedBits 4 3) (signedBits 4 1)
      (signedBits 3 2) (signedBits 3 (-1)) = -1 := by decide

example (pipeline : Pipeline)
    (trace : BoundaryTrace (ports 4 3 1)) : Prop :=
  contract 4 3 1 pipeline trace

end HTFFTTests.PipelinedSignedComplexMultiplyContract
