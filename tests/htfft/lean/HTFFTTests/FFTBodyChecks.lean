import HTFFT.Silean.FFT

namespace HTFFTTests.FFTBody

open Silean
open Silean.Modules
open HTFFT
open HTFFT.Silean

#check FFT.body
#check FFT.moduleStructure
#check FFT.design
#check FFT.place
#check FFT.structuralCertification
#check FFT.contract_of_body_trace
#check FFT.contract_of_execution
#check FFT.accuracy_of_execution
#print axioms FFT.structuralCertification
#print axioms FFT.contract_of_execution
#print axioms FFT.accuracy_of_execution

example (configuration : FFT.Configuration depth) :
    FFT.structuralChildren depth configuration .initialReorder =
      InitialReorder.moduleStructure depth configuration :=
  rfl

example (configuration : FFT.Configuration depth) :
    FFT.structuralChildren depth configuration .unrolled =
      UnrolledFFTNetwork.moduleStructure configuration.laneDepth
        configuration.unrolled configuration.prefixTable :=
  rfl

example (configuration : FFT.Configuration depth) :
    FFT.structuralChildren depth configuration .unrolledFirstDelay =
      OptionalShiftRegister.moduleStructure .bit
        configuration.unrolled.networkLatency :=
  rfl

example (configuration : FFT.Configuration depth) :
    FFT.structuralChildren depth configuration .stageChain =
      FFTStageChain.moduleStructure depth configuration :=
  rfl

example (configuration : FFT.Configuration depth) :
    FFT.structuralChildren depth configuration .finalReorder =
      FinalReorder.moduleStructure depth configuration :=
  rfl

example (configuration : FFT.Configuration depth) :
    (FFT.body depth configuration).instancePorts.ports .unrolled =
      UnrolledFFTNetwork.ports configuration.unrolled :=
  rfl

example (configuration : FFT.Configuration depth) :
    (FFT.body depth configuration).instancePorts.ports
        .unrolledFirstDelay =
      OptionalShiftRegister.ports .bit :=
  rfl

/-- The frame marker takes its own shift-register path around the unrolled
payload FFT and joins the payload only at the stage-chain boundary. -/
example (configuration : FFT.Configuration depth) :
    (FFT.body depth configuration).wiring.instanceInput
        .stageChain FFTStageChain.Input.i_first =
      (FFT.context depth configuration).instanceOutput
        .unrolledFirstDelay ShiftRegister.Output.output :=
  rfl

example (configuration : FFT.Configuration depth) :
    (FFT.body depth configuration).wiring.instanceInput
        .stageChain FFTStageChain.Input.i_data =
      (FFT.context depth configuration).instanceOutput
        .unrolled UnrolledFFTNetwork.Output.output :=
  rfl

end HTFFTTests.FFTBody
