import HTFFT.Silean.FFTStageChain.Internal.FFTStageChainStructural
import HTFFT.Silean.FFTStageChain.Internal.FFTStageChainVerification
import Silean.Semantics.StructuralObservation

/-! End-to-end certification of the concrete rolled-stage chain. -/

namespace HTFFT.Silean.FFTStageChain.Internal
open FFT

open _root_.Silean

/-- Every execution of the concrete chain satisfies the unchanged natural
framed contract for the complete rolled FFT suffix. -/
theorem contract_of_execution
    (depth : Nat) (configuration : Configuration depth)
    (twiddleFits : configuration.arithmetic.TwiddlesFit
      configuration.twiddleTable)
    (carrier : configuration.arithmetic.ProductCarriersCover)
    {initialState finalState :
      (FFTStageChain.moduleStructure depth configuration).State}
    {inputs : List (FFTStageChain.ports configuration).inputs.Values}
    {outputs : List (FFTStageChain.ports configuration).outputs.Values}
    (execution :
      (FFTStageChain.moduleStructure depth configuration).Executes
        initialState inputs outputs finalState) :
    FFTStageChain.contract configuration execution.toBoundaryTrace := by
  rcases execution.toBodyTrace with
    ⟨bodyTrace, wiring, parentTrace, childExecutions⟩
  have bodyContract := contract_of_body_trace configuration
    configuration.rolledStageLatency bodyTrace wiring (by rfl) (by
      intro index
      rcases childExecutions (.stage index) with
        ⟨childExecution, childTrace⟩
      have childContract := FFTStage.contract_of_execution
        configuration.arithmetic configuration.twiddleTable
        (FFTStageChain.stageGeometry configuration index)
        (configuration.rolledButterflyPipeline index)
        (configuration.rolledTwiddleDefinitionName index)
        twiddleFits carrier childExecution
      rw [childTrace] at childContract
      simpa [Configuration.rolledStageLatency,
        FFTStageChain.stageGeometry] using childContract)
  rwa [parentTrace] at bodyContract

end HTFFT.Silean.FFTStageChain.Internal
