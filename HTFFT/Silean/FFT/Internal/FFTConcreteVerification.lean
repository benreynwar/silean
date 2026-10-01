import HTFFT.Silean.FFT.Internal.FFTStructural
import HTFFT.Silean.FFT.Internal.FFTVerification
import Silean.Semantics.StructuralObservation

/-! End-to-end certification of the closed concrete FFT hierarchy. -/

namespace HTFFT.Silean.FFT.Internal

open _root_.Silean
open _root_.Silean.Modules

/-- Every execution of the closed hierarchy satisfies the natural framed
fixed-point FFT contract. -/
theorem contract_of_execution
    (depth : Nat) (configuration : Configuration depth)
    (twiddleFits : configuration.arithmetic.TwiddlesFit
      configuration.twiddleTable)
    (carrier : configuration.arithmetic.ProductCarriersCover)
    {initialState finalState :
      (FFT.moduleStructure depth configuration).State}
    {inputs : List (FFT.ports configuration).inputs.Values}
    {outputs : List (FFT.ports configuration).outputs.Values}
    (execution :
      (FFT.moduleStructure depth configuration).Executes
        initialState inputs outputs finalState) :
    FFT.contract configuration execution.toBoundaryTrace := by
  rcases execution.toBodyTrace with
    ⟨bodyTrace, wiring, parentTrace, childExecutions⟩
  have bodyContract := contract_of_body_trace configuration bodyTrace
    wiring
    (by
      rcases childExecutions (.initialReorder) with
        ⟨childExecution, childTrace⟩
      have childContract := InitialReorder.contract_of_execution depth
        configuration childExecution
      exact childTrace ▸ childContract)
    (by
      rcases childExecutions (.unrolled) with
        ⟨childExecution, childTrace⟩
      have childContract := UnrolledFFTNetwork.contract_of_execution
        configuration.unrolled configuration.prefixTable
        (configuration.unrolledTwiddlesFit twiddleFits)
        (configuration.unrolledProductCarriersCover carrier) childExecution
      exact childTrace ▸ childContract)
    (by
      rcases childExecutions (.unrolledFirstDelay) with
        ⟨childExecution, childTrace⟩
      have childContract := OptionalShiftRegister.contract_of_execution .bit
        configuration.unrolled.networkLatency childExecution
      exact childTrace ▸ childContract)
    (by
      rcases childExecutions (.stageChain) with
        ⟨childExecution, childTrace⟩
      have childContract := FFTStageChain.contract_of_execution configuration
        twiddleFits carrier childExecution
      exact childTrace ▸ childContract)
    (by
      rcases childExecutions (.finalReorder) with
        ⟨childExecution, childTrace⟩
      have childContract := FinalReorder.contract_of_execution depth
        configuration childExecution
      exact childTrace ▸ childContract)
  rwa [parentTrace] at bodyContract

end HTFFT.Silean.FFT.Internal
