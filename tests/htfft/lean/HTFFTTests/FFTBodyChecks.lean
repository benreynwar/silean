import HTFFT.Silean.FFT

namespace HTFFTTests.FFTBody

open Silean
open Silean.Modules
open HTFFT
open HTFFT.Silean

#check FFT.body
#check FFT.contract_of_body_trace

example (configuration : FFT.Configuration depth)
    (table : Fixed.TwiddleTable depth) :
    (FFT.body depth configuration table).instancePorts.ports .unrolled =
      UnrolledFFTNetwork.ports configuration.unrolled :=
  rfl

example (configuration : FFT.Configuration depth)
    (table : Fixed.TwiddleTable depth) :
    (FFT.body depth configuration table).instancePorts.ports
        .unrolledFirstDelay =
      OptionalShiftRegister.ports .bit :=
  rfl

/-- The frame marker takes its own shift-register path around the unrolled
payload FFT and joins the payload only at the stage-chain boundary. -/
example (configuration : FFT.Configuration depth)
    (table : Fixed.TwiddleTable depth) :
    (FFT.body depth configuration table).wiring.instanceInput
        .stageChain FFT.FFTStageChain.Input.i_first =
      (FFT.context depth configuration table).instanceOutput
        .unrolledFirstDelay ShiftRegister.Output.output :=
  rfl

example (configuration : FFT.Configuration depth)
    (table : Fixed.TwiddleTable depth) :
    (FFT.body depth configuration table).wiring.instanceInput
        .stageChain FFT.FFTStageChain.Input.i_data =
      (FFT.context depth configuration table).instanceOutput
        .unrolled UnrolledFFTNetwork.Output.output :=
  rfl

end HTFFTTests.FFTBody
