import HTFFT.Fixed.ButterflyCorrectness
import HTFFT.Silean.UnrolledFFTLayer.Internal.UnrolledFFTLayerStep
import Silean.Semantics.StructuralObservation

/-! All-time trace correctness of one generic unrolled FFT layer. -/

namespace HTFFT.Silean.UnrolledFFTLayer.Internal

open _root_.Silean
open HTFFT.FixedPoint

/-- Encoding and then decoding one representable stored twiddle recovers the
ordinary integer twiddle exactly. -/
theorem decode_twiddleValue
    (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (stage : Fin depth)
    (offset : Fin (2 ^ stage.val))
    (fits : ComplexFits (configuration.twiddleFormat stage)
      (table.value stage offset)) :
    PipelinedFixedButterfly.decodeComplex
        (configuration.twiddleFormat stage).width
        (twiddleValues configuration table stage offset) =
      table.value stage offset := by
  rw [show twiddleValues configuration table stage offset =
      PipelinedFixedButterfly.encodeComplex
        (configuration.twiddleFormat stage).width
        (table.value stage offset) by rfl]
  rw [PipelinedFixedButterfly.decodeComplex_encodeComplex]
  simpa [HTFFT.Butterfly.Fixed.wrapComplex] using
    (HTFFT.Butterfly.Fixed.wrapComplex_eq_of_fits fits)

/-- The child butterfly's natural packed calculation is exactly the pure
fixed-point calculation assigned to this layer position. -/
theorem childResultValue_eq
    (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (stage : Fin depth)
    (input : Fin (2 ^ depth) →
      (complexSignalType
        (configuration.boundaryFormat stage.castSucc)).Denote)
    (index : ButterflyIndex depth stage)
    (twiddleFits : ComplexFits (configuration.twiddleFormat stage)
      (table.value stage index.2)) :
    PipelinedFixedButterfly.resultValue
        (configuration.boundaryFormat stage.castSucc)
        (configuration.twiddleFormat stage)
        (input (sampleIndex index 0))
        (input (sampleIndex index 1))
        (twiddleValues configuration table stage index.2) =
      HTFFT.Butterfly.Fixed.butterfly
        (configuration.fixedConfig.butterfly stage)
        (decodeVector (configuration.boundaryFormat stage.castSucc) input
          (sampleIndex index 0))
        (decodeVector (configuration.boundaryFormat stage.castSucc) input
          (sampleIndex index 1))
        (table.value stage index.2) := by
  unfold PipelinedFixedButterfly.resultValue decodeVector
  rw [decode_twiddleValue configuration table stage index.2 twiddleFits]
  rw [configuration.butterfly_eq_fixedConfig]

/-- Every structural execution satisfies the natural vector-level layer
contract. -/
theorem contract_of_execution
    (depth : Nat) (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (stage : Fin depth)
    (twiddleFits : configuration.TwiddlesFit table)
    (carrier : configuration.ProductCarriersCover)
    {initialState finalState :
      (moduleStructure depth configuration table stage).State}
    {inputs : List (ports configuration stage).inputs.Values}
    {outputs : List (ports configuration stage).outputs.Values}
    (execution :
      (moduleStructure depth configuration table stage).Executes
        initialState inputs outputs finalState) :
    contract configuration table stage execution.toBoundaryTrace := by
  obtain ⟨hierarchy, observed, rootOutputs⟩ := execution.observe

  let butterflyExecution
      (index : ButterflyIndex depth stage) :=
    observed.child (.butterfly index)
  have butterflyContract (index : ButterflyIndex depth stage) :
      PipelinedFixedButterfly.contract
        (configuration.boundaryFormat stage.castSucc)
        (configuration.twiddleFormat stage)
        (configuration.butterflyPipeline stage)
        (butterflyExecution index).toBoundaryTrace := by
    apply PipelinedFixedButterfly.contract_of_execution
      (configuration.boundaryFormat stage.castSucc)
      (configuration.twiddleFormat stage)
      (configuration.butterflyPipeline stage)
      (carrier stage)

  unfold contract FixedLatency.Holds
  simp only [Trace.toBoundaryTrace_inputs, Trace.toBoundaryTrace_outputs]
  constructor
  · exact execution.length_eq
  · intro t inputInTrace outputInTrace
    have hierarchyLength : hierarchy.length = inputs.length :=
      observed.length_eq
    have sourceInHierarchy : t < hierarchy.length := by
      rw [hierarchyLength]
      exact inputInTrace
    have finalInHierarchy :
        t + configuration.layerLatency stage < hierarchy.length := by
      rw [hierarchyLength, ← execution.length_eq]
      exact outputInTrace

    let sourceStep := hierarchy.get ⟨t, sourceInHierarchy⟩
    let finalStep := hierarchy.get
      ⟨t + configuration.layerLatency stage, finalInHierarchy⟩
    have sourceSolution := observed.solution_at t sourceInHierarchy
    have finalSolution := observed.solution_at
      (t + configuration.layerLatency stage) finalInHierarchy
    have sourceAt := observed.input_at t sourceInHierarchy inputInTrace
    have finalAt := observed.output_at rootOutputs
      (t + configuration.layerLatency stage) finalInHierarchy outputInTrace
    change sourceStep.inputs = inputs.get ⟨t, inputInTrace⟩ at sourceAt
    change finalStep.outputs =
      outputs.get ⟨t + configuration.layerLatency stage, outputInTrace⟩
      at finalAt

    rw [← finalAt, ← sourceAt]
    funext sample
    let position := (HTFFT.Exact.layerIndexEquiv depth stage).symm sample
    let index : ButterflyIndex depth stage :=
      (position.group, position.offset)
    have indexEq : butterflyIndexOfSample (stage := stage) sample = index := by
      rfl
    have branchEq : branchOfSample stage sample = position.branch := by
      rfl

    have butterflyAt := FixedLatency.relation_at_of_trace
      (butterflyExecution index) (butterflyContract index) t
      (by simpa [butterflyExecution] using sourceInHierarchy)
      (by simpa [butterflyExecution, UnrolledFFT.Configuration.layerLatency]
        using finalInHierarchy)
    simp only [List.get_eq_getElem, List.getElem_map] at butterflyAt
    change
      (finalStep.children (.butterfly index)).outputs .upper =
          PipelinedFixedButterfly.encodeComplex
            (PipelinedFixedButterfly.outputComponentWidth
              (configuration.boundaryFormat stage.castSucc))
            (PipelinedFixedButterfly.resultValue
              (configuration.boundaryFormat stage.castSucc)
              (configuration.twiddleFormat stage)
              ((sourceStep.children (.butterfly index)).inputs .a)
              ((sourceStep.children (.butterfly index)).inputs .b)
              ((sourceStep.children (.butterfly index)).inputs .twiddle)).upper ∧
        (finalStep.children (.butterfly index)).outputs .lower =
          PipelinedFixedButterfly.encodeComplex
            (PipelinedFixedButterfly.outputComponentWidth
              (configuration.boundaryFormat stage.castSucc))
            (PipelinedFixedButterfly.resultValue
              (configuration.boundaryFormat stage.castSucc)
              (configuration.twiddleFormat stage)
              ((sourceStep.children (.butterfly index)).inputs .a)
              ((sourceStep.children (.butterfly index)).inputs .b)
              ((sourceStep.children (.butterfly index)).inputs .twiddle)).lower
      at butterflyAt
    have childInputs := butterflyInputs_of_solution sourceSolution index
    rw [childInputs.1, childInputs.2.1, childInputs.2.2] at butterflyAt
    have childResult := childResultValue_eq configuration table stage
      (sourceStep.inputs .input) index (twiddleFits stage index.2)
    rw [childResult] at butterflyAt

    rw [outputSample_of_solution finalSolution sample, indexEq, branchEq]
    change
      (if position.branch = 0 then
        castButterflyOutput configuration stage
          ((finalStep.children (.butterfly index)).outputs .upper)
       else
        castButterflyOutput configuration stage
          ((finalStep.children (.butterfly index)).outputs .lower)) = _
    by_cases upper : position.branch = 0
    · rw [if_pos upper, butterflyAt.1,
        cast_encodeComplex configuration stage]
      simp [encodeVector, resultValue, HTFFT.Fixed.butterflyLayer,
        position, index, upper, sampleIndex,
        _root_.HTFFT.Silean.UnrolledFFTLayer.Internal.position]
    · have lower : position.branch = 1 := by
        apply Fin.ext
        omega
      rw [if_neg upper, butterflyAt.2,
        cast_encodeComplex configuration stage]
      simp [encodeVector, resultValue, HTFFT.Fixed.butterflyLayer,
        position, index, lower, sampleIndex,
        _root_.HTFFT.Silean.UnrolledFFTLayer.Internal.position]

end HTFFT.Silean.UnrolledFFTLayer.Internal
