import HTFFT.Silean.FFT

namespace HTFFTTests.FFTStageChainBody

open Silean
open HTFFT
open HTFFT.Silean

#check FFT.FFTStageChain.body
#check FFT.FFTStageChain.contract_of_body_trace

example (configuration : FFT.Configuration depth)
    (table : Fixed.TwiddleTable depth)
    (index : FFT.FFTStageChain.StageIndex configuration) :
    (FFT.FFTStageChain.body depth configuration table).instancePorts.ports
        (.stage index) =
      FFTStage.ports configuration.arithmetic
        (FFT.FFTStageChain.stageGeometry configuration index) :=
  rfl

end HTFFTTests.FFTStageChainBody
