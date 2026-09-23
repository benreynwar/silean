import HTFFT.Silean.FFT.FFT

assert_not_imported HTFFT.Silean.FFT.Internal.FFTStructure
assert_not_imported HTFFT.Silean.FFT.Internal.FFTVerification

namespace HTFFTTests.FFTContract

open Silean
open HTFFT
open HTFFT.Silean

#check FFT.Configuration
#check FFT.naturalLayout
#check FFT.unpackInput
#check FFT.decodeInput
#check FFT.encodeOutput

#check FFT.InitialReorder.resultFrame
#check FFT.InitialReorder.contract
#check FFT.FFTStageChain.resultFrame
#check FFT.FFTStageChain.contract
#check FFT.FinalReorder.resultFrame
#check FFT.FinalReorder.contract

#check FFT.resultValue
#check FFT.resultFrame
#check FFT.contract

example (configuration : FFT.Configuration depth)
    (input : FFT.InputFrame configuration)
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount) :
    FFT.InitialReorder.resultFrame configuration input cycle lane =
      Exact.bitReverse (FFT.unpackInput configuration input)
        (FFT.naturalLayout configuration (cycle, lane)) :=
  rfl

end HTFFTTests.FFTContract
