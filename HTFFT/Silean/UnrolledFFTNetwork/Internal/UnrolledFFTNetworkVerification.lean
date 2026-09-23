import HTFFT.Silean.UnrolledFFTNetwork.Internal.UnrolledFFTNetworkStep
import Silean.Semantics.StructuralObservation

/-! All-time trace correctness of the generic unrolled FFT network. -/

namespace HTFFT.Silean.UnrolledFFTNetwork.Internal

open _root_.Silean
open _root_.Silean.Modules

private def boundaryResult
    (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (boundary : HTFFT.Exact.LayerBoundary depth)
    (input : Fin (2 ^ depth) →
      (UnrolledFFTLayer.complexSignalType
        (configuration.boundaryFormat 0)).Denote) :
    Fin (2 ^ depth) →
      (UnrolledFFTLayer.complexSignalType
        (configuration.boundaryFormat boundary)).Denote :=
  UnrolledFFTLayer.encodeVector (configuration.boundaryFormat boundary)
    (HTFFT.Fixed.applyButterflyLayers configuration.fixedConfig table
      (HTFFT.Exact.butterflyStagePrefix depth boundary)
      (UnrolledFFTLayer.decodeVector
        (configuration.boundaryFormat 0) input))

private def layerResult
    (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (stage : Fin depth)
    (input : Fin (2 ^ depth) →
      (UnrolledFFTLayer.complexSignalType
        (configuration.boundaryFormat stage.castSucc)).Denote) :
    Fin (2 ^ depth) →
      (UnrolledFFTLayer.complexSignalType
        (configuration.boundaryFormat stage.succ)).Denote :=
  UnrolledFFTLayer.encodeVector (configuration.boundaryFormat stage.succ)
    (UnrolledFFTLayer.resultValue configuration table stage input)

private theorem boundaryResult_zero
    (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) :
    boundaryResult configuration table 0 = id := by
  funext input
  simp [boundaryResult, HTFFT.Exact.butterflyStagePrefix,
    HTFFT.Exact.butterflyStages]

private theorem boundaryValue_canonical
    (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (boundary : HTFFT.Exact.LayerBoundary depth)
    (input : Fin (2 ^ depth) →
      (UnrolledFFTLayer.complexSignalType
        (configuration.boundaryFormat 0)).Denote) :
    (fun index => HTFFT.Butterfly.Fixed.wrapComplex
      (configuration.boundaryFormat boundary)
      (HTFFT.Fixed.applyButterflyLayers configuration.fixedConfig table
        (HTFFT.Exact.butterflyStagePrefix depth boundary)
        (UnrolledFFTLayer.decodeVector
          (configuration.boundaryFormat 0) input) index)) =
      HTFFT.Fixed.applyButterflyLayers configuration.fixedConfig table
        (HTFFT.Exact.butterflyStagePrefix depth boundary)
        (UnrolledFFTLayer.decodeVector
          (configuration.boundaryFormat 0) input) := by
  have inputCanonical :
      (fun index => HTFFT.Butterfly.Fixed.wrapComplex
        (configuration.fixedConfig.boundaryFormat 0)
        (UnrolledFFTLayer.decodeVector
          (configuration.boundaryFormat 0) input index)) =
        UnrolledFFTLayer.decodeVector
          (configuration.boundaryFormat 0) input := by
    funext index
    simp [UnrolledFFTLayer.decodeVector]
  simpa only [FFTConfiguration.fixedConfig_boundaryFormat] using
    HTFFT.Fixed.wrapComplex_applyButterflyStagePrefix_of_canonical
      configuration.fixedConfig table
      (UnrolledFFTLayer.decodeVector
        (configuration.boundaryFormat 0) input)
      inputCanonical boundary

private theorem layerResult_comp_boundaryResult
    (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (stage : Fin depth) :
    layerResult configuration table stage ∘
        boundaryResult configuration table stage.castSucc =
      boundaryResult configuration table stage.succ := by
  funext input
  unfold layerResult boundaryResult UnrolledFFTLayer.resultValue
  simp only [Function.comp_apply]
  rw [UnrolledFFTLayer.decodeVector_encodeVector]
  rw [boundaryValue_canonical configuration table stage.castSucc input]
  rw [HTFFT.Exact.butterflyStagePrefix_boundarySucc,
    HTFFT.Fixed.applyButterflyLayers_append]
  rfl

/-- Every structural execution satisfies the natural fixed-latency network
contract. -/
theorem contract_of_execution
    (depth : Nat) (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (twiddleFits : configuration.TwiddlesFit table)
    (carrier : configuration.ProductCarriersCover)
    {initialState finalState :
      (moduleStructure depth configuration table).State}
    {inputs : List (ports configuration).inputs.Values}
    {outputs : List (ports configuration).outputs.Values}
    (execution :
      (moduleStructure depth configuration table).Executes
        initialState inputs outputs finalState) :
    contract configuration table execution.toBoundaryTrace := by
  obtain ⟨hierarchy, observed, rootOutputs⟩ := execution.observe

  let parentInputs := hierarchy.map fun step => step.inputs .input
  let parentOutputs := hierarchy.map fun step => step.outputs .output
  let boundaryInputs (boundary : HTFFT.Exact.LayerBoundary depth) :=
    hierarchy.map fun step =>
      (step.children (.boundaryDelay boundary)).inputs .input
  let boundaryOutputs (boundary : HTFFT.Exact.LayerBoundary depth) :=
    hierarchy.map fun step =>
      (step.children (.boundaryDelay boundary)).outputs .output
  let layerInputs (stage : Fin depth) := hierarchy.map fun step =>
    (step.children (.layer stage)).inputs .input
  let layerOutputs (stage : Fin depth) := hierarchy.map fun step =>
    (step.children (.layer stage)).outputs .output

  have boundaryComputation
      (boundary : HTFFT.Exact.LayerBoundary depth) :
      FixedLatency.Computes (configuration.boundaryLatency boundary) id
        (boundaryInputs boundary) (boundaryOutputs boundary) := by
    have childExecution := observed.child (.boundaryDelay boundary)
    have childContract := OptionalShiftRegister.contract_of_execution
      (samplesType configuration boundary)
      (configuration.boundaryLatency boundary) childExecution
    unfold OptionalShiftRegister.contract at childContract
    have projected := FixedLatency.computes_of_holds_projection
      (function := id)
      (fun input :
          (OptionalShiftRegister.ports
            (samplesType configuration boundary)).inputs.Values =>
        input .input)
      (fun output :
          (OptionalShiftRegister.ports
            (samplesType configuration boundary)).outputs.Values =>
        output .output)
      childContract
    simp only [Trace.toBoundaryTrace_inputs,
      Trace.toBoundaryTrace_outputs] at projected
    change FixedLatency.Computes
      (configuration.boundaryLatency boundary) id
      ((hierarchy.map fun step =>
        (step.children (.boundaryDelay boundary)).inputs).map
          (fun input => input .input))
      ((hierarchy.map fun step =>
        (step.children (.boundaryDelay boundary)).outputs).map
          (fun output => output .output)) at projected
    rw [List.map_map, List.map_map] at projected
    exact projected

  have layerComputation (stage : Fin depth) :
      FixedLatency.Computes (configuration.layerLatency stage)
        (layerResult configuration table stage)
        (layerInputs stage) (layerOutputs stage) := by
    have childExecution := observed.child (.layer stage)
    have childContract := UnrolledFFTLayer.contract_of_execution
      configuration table stage twiddleFits carrier childExecution
    unfold UnrolledFFTLayer.contract at childContract
    have projected := FixedLatency.computes_of_holds_projection
      (function := layerResult configuration table stage)
      (fun input : (UnrolledFFTLayer.ports configuration stage).inputs.Values =>
        input .input)
      (fun output :
          (UnrolledFFTLayer.ports configuration stage).outputs.Values =>
        output .output)
      childContract
    simp only [Trace.toBoundaryTrace_inputs,
      Trace.toBoundaryTrace_outputs] at projected
    change FixedLatency.Computes (configuration.layerLatency stage)
      (layerResult configuration table stage)
      ((hierarchy.map fun step =>
        (step.children (.layer stage)).inputs).map
          (fun input => input .input))
      ((hierarchy.map fun step =>
        (step.children (.layer stage)).outputs).map
          (fun output => output .output)) at projected
    rw [List.map_map, List.map_map] at projected
    exact projected

  have initialBoundaryInputs : boundaryInputs 0 = parentInputs := by
    apply List.map_congr_left
    intro step member
    exact initialBoundaryInput_of_solution
      (observed.solution_of_mem step member)

  have layerInputsEqual (stage : Fin depth) :
      layerInputs stage = boundaryOutputs stage.castSucc := by
    apply List.map_congr_left
    intro step member
    exact layerInput_of_solution
      (observed.solution_of_mem step member) stage

  have successorBoundaryInputs (stage : Fin depth) :
      boundaryInputs stage.succ = layerOutputs stage := by
    apply List.map_congr_left
    intro step member
    exact successorBoundaryInput_of_solution
      (observed.solution_of_mem step member) stage

  have finalOutputs : parentOutputs = boundaryOutputs (Fin.last depth) := by
    apply List.map_congr_left
    intro step member
    exact output_of_solution (observed.solution_of_mem step member)

  have boundaryPrefix (boundary : HTFFT.Exact.LayerBoundary depth) :
      FixedLatency.Computes (configuration.latencyTo boundary)
        (boundaryResult configuration table boundary)
        parentInputs (boundaryOutputs boundary) := by
    induction boundary using Fin.induction with
    | zero =>
        rw [UnrolledFFT.Configuration.latencyTo_zero,
          boundaryResult_zero configuration table]
        exact FixedLatency.computes_congr_inputs initialBoundaryInputs
          (boundaryComputation 0)
    | succ stage induction =>
        have layer := FixedLatency.computes_congr_inputs
          (layerInputsEqual stage) (layerComputation stage)
        have throughLayer := FixedLatency.computes_serial induction layer
        have delay := FixedLatency.computes_congr_inputs
          (successorBoundaryInputs stage)
          (boundaryComputation stage.succ)
        have throughBoundary :=
          FixedLatency.computes_serial throughLayer delay
        change FixedLatency.Computes
          ((configuration.latencyTo stage.castSucc +
              configuration.layerLatency stage) +
            configuration.boundaryLatency stage.succ)
          (layerResult configuration table stage ∘
            boundaryResult configuration table stage.castSucc)
          parentInputs (boundaryOutputs stage.succ) at throughBoundary
        rw [layerResult_comp_boundaryResult configuration table stage]
          at throughBoundary
        rw [UnrolledFFT.Configuration.latencyTo_succ]
        simpa only [Nat.add_assoc] using throughBoundary

  unfold contract FixedLatency.Holds
  simp only [Trace.toBoundaryTrace_inputs, Trace.toBoundaryTrace_outputs]
  have complete := boundaryPrefix (Fin.last depth)
  rw [UnrolledFFT.Configuration.latencyTo_final] at complete
  have parentInputsOriginal : parentInputs = inputs.map fun input => input .input := by
    unfold parentInputs
    calc
      hierarchy.map (fun step => step.inputs .input) =
          (hierarchy.map HierStep.inputs).map (fun input => input .input) := by
        simp [List.map_map]
      _ = inputs.map (fun input => input .input) :=
        congrArg (List.map fun input => input .input)
          observed.hierarchy_inputs
  have parentOutputsOriginal :
      parentOutputs = outputs.map fun output => output .output := by
    unfold parentOutputs
    calc
      hierarchy.map (fun step => step.outputs .output) =
          (hierarchy.map HierStep.outputs).map
            (fun output => output .output) := by
        simp [List.map_map]
      _ = outputs.map (fun output => output .output) :=
        congrArg (List.map fun output => output .output) rootOutputs
  rw [← finalOutputs, parentInputsOriginal, parentOutputsOriginal] at complete
  have projected := FixedLatency.computes_map_inputs
    (fun input : (ports configuration).inputs.Values => input .input)
    complete
  unfold FixedLatency.Computes FixedLatency.Relates at projected
  unfold FixedLatency.Relates
  constructor
  · exact execution.length_eq
  · intro t inputInTrace outputInTrace
    have mappedOutputInTrace :
        t + configuration.networkLatency <
          (outputs.map fun output => output .output).length := by
      rw [List.length_map]
      exact outputInTrace
    have related := projected.2 t inputInTrace mappedOutputInTrace
    have outputAt :
        (outputs.map fun output => output .output).get
            ⟨t + configuration.networkLatency, mappedOutputInTrace⟩ =
          (outputs.get
            ⟨t + configuration.networkLatency, outputInTrace⟩) .output := by
      simp
    change
      (outputs.map fun output => output .output).get
          ⟨t + configuration.networkLatency, mappedOutputInTrace⟩ =
        boundaryResult configuration table (Fin.last depth)
          ((inputs.get ⟨t, inputInTrace⟩) .input) at related
    rw [outputAt] at related
    simpa only [List.get_eq_getElem, List.getElem_map,
      Function.comp_apply, boundaryResult, resultValue,
      HTFFT.Exact.butterflyStagePrefix_final] using related

end HTFFT.Silean.UnrolledFFTNetwork.Internal
