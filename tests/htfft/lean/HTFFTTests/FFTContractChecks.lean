import HTFFT.Silean.FFT.FFTCorrectness

assert_not_imported HTFFT.Silean.FFT.Internal.FFTStructure
assert_not_imported HTFFT.Silean.FFT.Internal.FFTVerification

namespace HTFFTTests.FFTContract

open Silean
open HTFFT
open HTFFT.Silean

#check FFT.Configuration
#check FFT.Configuration.twiddleTable
#check FFT.Configuration.prefixTable
#check FFT.Configuration.twiddleAccuracy
#print axioms FFT.Configuration.twiddleAccuracy
#check FFT.Configuration.safeInputMagnitude
#check FFT.Configuration.outputBounds
#check FFT.Configuration.outputError
#check FFT.Configuration.rangeSafe
#check FFT.naturalLayout
#check FFT.unpackInput
#check FFT.decodeInput
#check FFT.encodeOutput
#check FFT.decodeOutput
#check FFT.decodeOutput_encodeOutput
#check FFT.decodeOutput_encodeOutput_of_canonical

#check InitialReorder.resultFrame
#check InitialReorder.contract
#check FFTStageChain.resultFrame
#check FFTStageChain.contract
#check FinalReorder.resultFrame
#check FinalReorder.contract

#check FFT.resultValue
#check FFT.resultFrame
#check FFT.contract
#check FFT.resultValue_canonical
#check FFT.decodeOutput_resultFrame
#check FFT.output_within
#check FFT.output_pointwise_dft
#check FFT.accuracy_of_contract

example (configuration : FFT.Configuration depth)
    (input : FFT.InputFrame configuration)
    (cycle : Fin configuration.frameLength)
    (lane : Fin configuration.laneCount) :
    InitialReorder.resultFrame configuration input cycle lane =
      Exact.bitReverse (FFT.unpackInput configuration input)
        (FFT.naturalLayout configuration (cycle, lane)) :=
  rfl

end HTFFTTests.FFTContract
