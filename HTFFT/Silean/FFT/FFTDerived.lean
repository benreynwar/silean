import HTFFT.Silean.FFT.Internal.FFTConcreteVerification
import HTFFT.Silean.FFT.FFTCorrectness

/-! Public placement, certification, and correctness results for the complete
FFT hierarchy. -/

namespace HTFFT.Silean.FFT

open _root_.Silean
open _root_.Silean.Modules
open _root_.Silean.Authoring.CircuitDescription

/-- Place the complete concrete streaming FFT hierarchy. -/
noncomputable def place
    (configuration : Configuration depth)
    (i_first : Net .bit)
    (i_data : Net (.vector configuration.laneCount
      (UnrolledFFTLayer.complexSignalType
        (configuration.arithmetic.boundaryFormat 0)))) :
    Builder (ports.OutputNets configuration) :=
  ports.placeIndexed configuration "fft"
    (moduleStructure depth configuration)
    (naming depth configuration) i_first i_data

attribute [circuit_description] place

/-- The complete FFT hierarchy has exactly one structural solution for every
boundary input and physical state. -/
theorem structuralCertification
    (configuration : Configuration depth) :
    ModuleStructuralCertification
      (moduleStructure depth configuration) :=
  Internal.structuralCertification depth configuration

/-- The permanent top-level body satisfies the natural FFT contract whenever
its functional children and separate marker shift register satisfy their
public boundary-trace contracts. -/
theorem contract_of_body_trace
    (configuration : Configuration depth)
    (trace : (body depth configuration).Trace)
    (wiring : trace.WiringHolds)
    (initialCorrect : InitialReorder.contract configuration
      (trace.child .initialReorder))
    (unrolledCorrect : UnrolledFFTNetwork.contract configuration.unrolled
      configuration.prefixTable (trace.child .unrolled))
    (markerDelayCorrect : OptionalShiftRegister.contract .bit
      configuration.unrolled.networkLatency
      (trace.child .unrolledFirstDelay))
    (stageChainCorrect : FFTStageChain.contract configuration
      (trace.child .stageChain))
    (finalCorrect : FinalReorder.contract configuration
      (trace.child .finalReorder)) :
    contract configuration trace.parent :=
  Internal.contract_of_body_trace configuration trace wiring
    initialCorrect unrolledCorrect markerDelayCorrect stageChainCorrect
    finalCorrect

/-- Every execution of the closed hierarchy satisfies the natural framed
fixed-point FFT contract. -/
theorem contract_of_execution
    (configuration : Configuration depth)
    (twiddleFits : configuration.arithmetic.TwiddlesFit
      configuration.twiddleTable)
    (carrier : configuration.arithmetic.ProductCarriersCover)
    {initialState finalState :
      (moduleStructure depth configuration).State}
    {inputs : List (ports configuration).inputs.Values}
    {outputs : List (ports configuration).outputs.Values}
    (execution :
      (moduleStructure depth configuration).Executes
        initialState inputs outputs finalState) :
    contract configuration execution.toBoundaryTrace :=
  Internal.contract_of_execution depth configuration
    twiddleFits carrier execution

/-- End-to-end accuracy of every execution of the closed hardware hierarchy.

A complete input frame beginning at `start` and carrying no later `i_first`
produces an `o_first`-marked natural-order output frame after exactly
`totalLatency` cycles. Each decoded output is within the explicit propagated
error bound of Mathlib's ordinary unnormalized DFT at the same natural index.
-/
theorem accuracy_of_execution
    (configuration : Configuration depth)
    (twiddleError : Fin depth → ℝ)
    (carrier : configuration.arithmetic.ProductCarriersCover)
    {initialState finalState :
      (moduleStructure depth configuration).State}
    {inputs : List (ports configuration).inputs.Values}
    {outputs : List (ports configuration).outputs.Values}
    (execution :
      (moduleStructure depth configuration).Executes
        initialState inputs outputs finalState)
    (start : Nat)
    (tracePresent :
      start + configuration.totalLatency + configuration.frameLength ≤
        execution.toBoundaryTrace.inputs.length)
    (inputStarts : FramedLatency.Starts configuration.frameLength_pos
      (fun input : (ports configuration).inputs.Values =>
        input .i_first = true)
      (FramedLatency.window execution.toBoundaryTrace.inputs start
        (by omega)))
    (exactInput : HTFFT.Exact.Vector depth ℂ)
    (initial : HTFFT.Fixed.Bounds)
    (initialNonnegative : initial.Nonnegative)
    (twiddleAccuracy : HTFFT.Fixed.TwiddleAccuracy
      configuration.arithmetic.fixedConfig configuration.twiddleTable twiddleError)
    (inputMagnitude : HTFFT.Fixed.MagnitudeBound
      initial.magnitude exactInput)
    (inputWithin : HTFFT.Fixed.Within initial.error
      (HTFFT.Fixed.decodeVector configuration.arithmetic.fixedConfig 0
        (decodeInput configuration
          (inputFrameAt configuration execution.toBoundaryTrace start
            (by omega)))) exactInput)
    (noOverflow : HTFFT.Fixed.NoOverflow
      configuration.arithmetic.fixedConfig configuration.twiddleTable
      (decodeInput configuration
        (inputFrameAt configuration execution.toBoundaryTrace start
          (by omega)))) :
    FramedLatency.Starts configuration.frameLength_pos
        (fun output : (ports configuration).outputs.Values =>
          output .o_first = true)
        (FramedLatency.window execution.toBoundaryTrace.outputs
          (start + configuration.totalLatency) (by
            simpa [BoundaryTrace.outputs, BoundaryTrace.inputs] using
              tracePresent)) ∧
      ∀ index : Fin (2 ^ depth),
        ‖decodeOutput configuration
              (outputFrameAt configuration execution.toBoundaryTrace
                (start + configuration.totalLatency) (by
                  simpa [BoundaryTrace.outputs, BoundaryTrace.inputs] using
                    tracePresent)) index -
            ZMod.dft (HTFFT.Exact.toZModVector exactInput)
              (HTFFT.Exact.zmodIndexEquiv depth index)‖ ≤
          (HTFFT.Fixed.boundsAt configuration.arithmetic.fixedConfig
            twiddleError initial (Fin.last depth)).error := by
  have twiddleFits := FFTConfiguration.TwiddlesFit.ofAccuracy
    configuration.arithmetic configuration.twiddleTable twiddleError twiddleAccuracy
  have hardwareContract := contract_of_execution configuration
    twiddleFits carrier execution
  exact accuracy_of_contract configuration twiddleError
    execution.toBoundaryTrace hardwareContract start tracePresent inputStarts
    exactInput initial initialNonnegative twiddleAccuracy inputMagnitude
    inputWithin noOverflow

end HTFFT.Silean.FFT
