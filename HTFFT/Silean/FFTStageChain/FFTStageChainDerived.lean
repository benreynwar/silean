import HTFFT.Silean.FFTStageChain.Internal.FFTStageChainConcreteVerification

/-! Public placement and correctness declarations for the rolled-stage chain. -/

namespace HTFFT.Silean.FFTStageChain
open FFT

open _root_.Silean
open _root_.Silean.Authoring.CircuitDescription

/-- Place the complete concrete rolled FFT suffix. -/
noncomputable def place
    (configuration : Configuration depth)
    (i_first : Net .bit)
    (i_data : Net (.vector configuration.laneCount
      (UnrolledFFTLayer.complexSignalType
        (configuration.arithmetic.boundaryFormat
          configuration.prefixBoundary)))) :
    Builder (ports.OutputNets configuration) :=
  ports.placeIndexed configuration "fft_stage_chain"
    (moduleStructure depth configuration)
    (naming depth configuration) i_first i_data

attribute [circuit_description] place

/-- The complete concrete chain hierarchy has exactly one structural solution
for every boundary input and physical state. -/
theorem structuralCertification
    (configuration : Configuration depth) :
    ModuleStructuralCertification
      (moduleStructure depth configuration) :=
  Internal.structuralCertification depth configuration

/-- The permanent rolled-stage body satisfies the natural chain contract when
every stage satisfies its public boundary-trace contract and the supplied
stage latencies sum to the chain latency. -/
theorem contract_of_body_trace
    (configuration : Configuration depth)
    (stageLatency : StageIndex configuration → Nat)
    (trace : (body depth configuration).Trace)
    (wiring : trace.WiringHolds)
    (latencyMatches :
      accumulatedLatency configuration stageLatency =
        configuration.stageChainLatency)
    (stageCorrect : ∀ index,
      FFTStage.contract configuration.arithmetic configuration.twiddleTable
        (stageGeometry configuration index) (stageLatency index)
        (trace.child (.stage index))) :
    contract configuration trace.parent :=
  Internal.contract_of_body_trace configuration stageLatency trace
    wiring latencyMatches stageCorrect

/-- Every concrete chain execution satisfies the unchanged natural framed
contract for the rolled FFT suffix. -/
theorem contract_of_execution
    (configuration : Configuration depth)
    {initialState finalState :
      (moduleStructure depth configuration).State}
    {inputs : List (ports configuration).inputs.Values}
    {outputs : List (ports configuration).outputs.Values}
    (execution :
      (moduleStructure depth configuration).Executes
        initialState inputs outputs finalState) :
    contract configuration execution.toBoundaryTrace :=
  Internal.contract_of_execution depth configuration
    execution

end HTFFT.Silean.FFTStageChain
