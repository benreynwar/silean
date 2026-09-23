import HTFFT.Silean.UnrolledFFT.UnrolledFFTCorrectness

assert_not_imported HTFFT.Silean.UnrolledFFT.Internal.UnrolledFFTStructure
assert_not_imported HTFFT.Silean.UnrolledFFT.Internal.UnrolledFFTVerification

namespace HTFFTTests.UnrolledFFTContract

open Silean
open HTFFT
open HTFFT.FixedPoint
open HTFFT.Silean

#check UnrolledFFT.contract
#check UnrolledFFT.resultValue
#check UnrolledFFT.decodeOutput_encode_resultValue
#check UnrolledFFT.output_within
#check UnrolledFFT.output_pointwise_dft

end HTFFTTests.UnrolledFFTContract
