import HTFFT.Fixed.LayeredRangeCorrectness
import HTFFT.Silean.FFT.FFT

/-! Representation and numerical bridges for the complete streaming FFT
contract. -/

namespace HTFFT.Silean.FFT

open _root_.Silean

/-- Extract the naturally ordered input payload frame beginning at an
absolute boundary-trace position. -/
def inputFrameAt (configuration : Configuration depth)
    (trace : BoundaryTrace (ports configuration)) (start : Nat)
    (within : start + configuration.frameLength ≤ trace.inputs.length) :
    InputFrame configuration :=
  fun cycle => (FramedLatency.window trace.inputs start within cycle) .i_data

/-- Extract the naturally ordered output payload frame beginning at an
absolute boundary-trace position. -/
def outputFrameAt (configuration : Configuration depth)
    (trace : BoundaryTrace (ports configuration)) (start : Nat)
    (within : start + configuration.frameLength ≤ trace.outputs.length) :
    OutputFrame configuration :=
  fun cycle => (FramedLatency.window trace.outputs start within cycle) .o_data

/-- The pure result named by the top-level contract is already represented
canonically at the hardware output width. -/
theorem resultValue_canonical
    (configuration : Configuration depth)
    (input : InputFrame configuration) :
    (fun index => HTFFT.Butterfly.Fixed.wrapComplex
      (configuration.arithmetic.boundaryFormat (Fin.last depth))
      (resultValue configuration input index)) =
      resultValue configuration input := by
  have inputCanonical :
      (fun index => HTFFT.Butterfly.Fixed.wrapComplex
        (configuration.arithmetic.boundaryFormat 0)
        (decodeInput configuration input index)) =
        decodeInput configuration input := by
    funext index
    simp [decodeInput, UnrolledFFTLayer.decodeVector]
  simpa only [resultValue,
    FFTConfiguration.fixedConfig_boundaryFormat] using
    HTFFT.Fixed.wrapComplex_layeredFFT_of_canonical
      configuration.arithmetic.fixedConfig configuration.twiddleTable
      (decodeInput configuration input) inputCanonical

/-- Encoding the contract result and decoding the natural hardware frame loses
no information. No-overflow is not needed for this representation fact. -/
@[simp] theorem decodeOutput_resultFrame
    (configuration : Configuration depth)
    (input : InputFrame configuration) :
    decodeOutput configuration (resultFrame configuration input) =
      HTFFT.Fixed.decodeVector configuration.arithmetic.fixedConfig
        (Fin.last depth) (resultValue configuration input) := by
  unfold resultFrame
  exact decodeOutput_encodeOutput_of_canonical configuration _
    (resultValue_canonical configuration input)

/-- One correct external output frame inherits the pure fixed-point network's
global error bound. -/
theorem output_within
    (configuration : Configuration depth)
    (input : InputFrame configuration)
    (output : OutputFrame configuration)
    (exactInput : HTFFT.Exact.Vector depth ℂ)
    (initial : HTFFT.Fixed.Bounds)
    (outputCorrect : output = resultFrame configuration input)
    (initialNonnegative : initial.Nonnegative)
    (inputMagnitude : HTFFT.Fixed.MagnitudeBound
      initial.magnitude exactInput)
    (inputWithin : HTFFT.Fixed.Within initial.error
      (HTFFT.Fixed.decodeVector configuration.arithmetic.fixedConfig 0
        (decodeInput configuration input)) exactInput)
    (inputFitsRange :
      initial.total ≤ configuration.safeInputMagnitude) :
    HTFFT.Fixed.Within
      (configuration.outputError initial)
      (decodeOutput configuration output)
      (HTFFT.Exact.layeredFFT depth exactInput) := by
  subst output
  rw [decodeOutput_resultFrame]
  exact HTFFT.Fixed.layeredFFT_within_of_rangeSafe
    configuration.arithmetic.fixedConfig configuration.twiddleTable
    configuration.twiddleError
    (decodeInput configuration input) exactInput initial initialNonnegative
    configuration.twiddleAccuracy inputMagnitude inputWithin
    (configuration.rangeSafe initial inputFitsRange)

/-- Pointwise Mathlib-DFT form of the complete-frame numerical bridge. The DFT
is the ordinary unnormalized transform and `index` is in natural order. -/
theorem output_pointwise_dft
    (configuration : Configuration depth)
    (input : InputFrame configuration)
    (output : OutputFrame configuration)
    (exactInput : HTFFT.Exact.Vector depth ℂ)
    (initial : HTFFT.Fixed.Bounds)
    (outputCorrect : output = resultFrame configuration input)
    (initialNonnegative : initial.Nonnegative)
    (inputMagnitude : HTFFT.Fixed.MagnitudeBound
      initial.magnitude exactInput)
    (inputWithin : HTFFT.Fixed.Within initial.error
      (HTFFT.Fixed.decodeVector configuration.arithmetic.fixedConfig 0
        (decodeInput configuration input)) exactInput)
    (inputFitsRange :
      initial.total ≤ configuration.safeInputMagnitude)
    (index : Fin (2 ^ depth)) :
    ‖decodeOutput configuration output index -
        ZMod.dft (HTFFT.Exact.toZModVector exactInput)
      (HTFFT.Exact.zmodIndexEquiv depth index)‖ ≤
      configuration.outputError initial := by
  have bounded := output_within configuration input output
    exactInput initial outputCorrect initialNonnegative
    inputMagnitude inputWithin inputFitsRange index
  rw [HTFFT.Exact.layeredFFT_agreesWithDFT] at bounded
  exact bounded

/-- A valid marked input frame in any trace satisfying the top-level contract
produces an aligned output marker and the stated pointwise DFT accuracy bound
after exactly `totalLatency` cycles. -/
theorem accuracy_of_contract
    (configuration : Configuration depth)
    (trace : BoundaryTrace (ports configuration))
    (holds : contract configuration trace)
    (start : Nat)
    (tracePresent :
      start + configuration.totalLatency + configuration.frameLength ≤
        trace.inputs.length)
    (inputStarts : FramedLatency.Starts configuration.frameLength_pos
      (fun input : (ports configuration).inputs.Values =>
        input .i_first = true)
      (FramedLatency.window trace.inputs start (by omega)))
    (exactInput : HTFFT.Exact.Vector depth ℂ)
    (initial : HTFFT.Fixed.Bounds)
    (initialNonnegative : initial.Nonnegative)
    (inputMagnitude : HTFFT.Fixed.MagnitudeBound
      initial.magnitude exactInput)
    (inputWithin : HTFFT.Fixed.Within initial.error
      (HTFFT.Fixed.decodeVector configuration.arithmetic.fixedConfig 0
        (decodeInput configuration
          (inputFrameAt configuration trace start (by omega)))) exactInput)
    (inputFitsRange :
      initial.total ≤ configuration.safeInputMagnitude) :
    FramedLatency.Starts configuration.frameLength_pos
        (fun output : (ports configuration).outputs.Values =>
          output .o_first = true)
        (FramedLatency.window trace.outputs
          (start + configuration.totalLatency) (by
            simpa [BoundaryTrace.outputs, BoundaryTrace.inputs] using
              tracePresent)) ∧
      ∀ index : Fin (2 ^ depth),
        ‖decodeOutput configuration
              (outputFrameAt configuration trace
                (start + configuration.totalLatency) (by
                  simpa [BoundaryTrace.outputs, BoundaryTrace.inputs] using
                    tracePresent)) index -
            ZMod.dft (HTFFT.Exact.toZModVector exactInput)
              (HTFFT.Exact.zmodIndexEquiv depth index)‖ ≤
          configuration.outputError initial := by
  unfold contract FramedLatency.Holds at holds
  have inputPresent :
      start + configuration.frameLength ≤ trace.inputs.length := by omega
  have outputPresent :
      start + configuration.totalLatency + configuration.frameLength ≤
        trace.outputs.length := by
    simpa [BoundaryTrace.outputs, BoundaryTrace.inputs] using tracePresent
  have observed := FramedLatency.relation_at holds start inputPresent
    outputPresent inputStarts
  have outputCorrect :
      outputFrameAt configuration trace
          (start + configuration.totalLatency) (by omega) =
        resultFrame configuration
          (inputFrameAt configuration trace start inputPresent) := by
    unfold frameRelation carriedRelation inputObservation outputObservation at observed
    unfold inputFrameAt outputFrameAt
    exact observed.2
  constructor
  · exact observed.1
  · intro index
    exact output_pointwise_dft configuration
      (inputFrameAt configuration trace start inputPresent)
      (outputFrameAt configuration trace
        (start + configuration.totalLatency) (by omega))
      exactInput initial outputCorrect initialNonnegative
      inputMagnitude inputWithin inputFitsRange index

end HTFFT.Silean.FFT
