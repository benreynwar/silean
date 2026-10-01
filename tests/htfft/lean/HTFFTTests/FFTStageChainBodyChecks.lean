import HTFFT.Silean.FFTStageChain

namespace HTFFTTests.FFTStageChainBody

open Silean
open HTFFT
open HTFFT.Silean

#check FFTStageChain.body
#check FFTStageChain.moduleStructure
#check FFTStageChain.design
#check FFTStageChain.place
#check FFTStageChain.structuralCertification
#check FFTStageChain.contract_of_body_trace
#check FFTStageChain.contract_of_execution
#print axioms FFTStageChain.structuralCertification
#print axioms FFTStageChain.contract_of_execution

example (configuration : FFT.Configuration depth)
    (index : FFTStageChain.StageIndex configuration) :
    (FFTStageChain.body depth configuration).instancePorts.ports
        (.stage index) =
      FFTStage.ports configuration.arithmetic
        (FFTStageChain.stageGeometry configuration index) :=
  rfl

example (configuration : FFT.Configuration depth)
    (index : FFTStageChain.StageIndex configuration) :
    FFTStageChain.structuralChildren depth configuration
        (.stage index) =
      FFTStage.moduleStructure depth configuration.arithmetic
        configuration.twiddleTable
        (FFTStageChain.stageGeometry configuration index)
        (configuration.rolledButterflyPipeline index)
        (configuration.rolledTwiddleDefinitionName index) :=
  rfl

end HTFFTTests.FFTStageChainBody
