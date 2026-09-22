import HTFFT.Silean.PipelinedFixedButterfly.Internal.PipelinedFixedButterflyStep
import Silean.Semantics.StructuralObservation

/-! All-time trace correctness of the structural fixed-point butterfly. -/

namespace HTFFT.Silean.PipelinedFixedButterfly.Internal

open _root_.Silean
open _root_.Silean.Modules
open HTFFT.FixedPoint

/-- Every structural execution satisfies the natural packed fixed-latency
contract whenever the generic multiplier carrier covers the selected product
boundary width. -/
theorem contract_of_execution
    (dataFormat twiddleFormat : Format) (pipeline : Pipeline)
    (carrier : ProductCarrierCoversData dataFormat twiddleFormat)
    {initialState finalState :
      (moduleStructure dataFormat.width dataFormat.fractionalBits
        twiddleFormat.width twiddleFormat.fractionalBits
        pipeline.registerInputs pipeline.complexMultiply.multiplierLatency
        pipeline.complexMultiply.registerBeforeRounding
        pipeline.registerProduct pipeline.registerOutputs).State}
    {inputs : List (ports dataFormat twiddleFormat).inputs.Values}
    {outputs : List (ports dataFormat twiddleFormat).outputs.Values}
    (execution :
      (moduleStructure dataFormat.width dataFormat.fractionalBits
        twiddleFormat.width twiddleFormat.fractionalBits
        pipeline.registerInputs pipeline.complexMultiply.multiplierLatency
        pipeline.complexMultiply.registerBeforeRounding
        pipeline.registerProduct pipeline.registerOutputs).Executes
          initialState inputs outputs finalState) :
    contract dataFormat twiddleFormat pipeline execution.toBoundaryTrace := by
  rcases dataFormat with ⟨dataWidth, dataFractionalBits⟩
  rcases twiddleFormat with ⟨twiddleWidth, twiddleFractionalBits⟩
  let dataFormat : Format := ⟨dataWidth, dataFractionalBits⟩
  let twiddleFormat : Format := ⟨twiddleWidth, twiddleFractionalBits⟩
  obtain ⟨hierarchy, observed, rootOutputs⟩ := execution.observe

  have aInputExecution := observed.child (.aInputDelay)
  have bInputExecution := observed.child (.bInputDelay)
  have twiddleInputExecution := observed.child (.twiddleInputDelay)
  have productExecution := observed.child (.product)
  have productDelayExecution := observed.child (.productDelay)
  have aAlignExecution := observed.child (.aAlignDelay)
  have upperOutputExecution := observed.child (.upperOutputDelay)
  have lowerOutputExecution := observed.child (.lowerOutputDelay)
  simp only [structuralChildren] at aInputExecution bInputExecution twiddleInputExecution productExecution productDelayExecution aAlignExecution upperOutputExecution lowerOutputExecution

  have aInputContract := OptionalShiftRegister.contract_of_execution
    (.vector (dataFormat.width + dataFormat.width) .bit)
    (Bool.toNat pipeline.registerInputs) aInputExecution
  have bInputContract := OptionalShiftRegister.contract_of_execution
    (.vector (dataFormat.width + dataFormat.width) .bit)
    (Bool.toNat pipeline.registerInputs) bInputExecution
  have twiddleInputContract := OptionalShiftRegister.contract_of_execution
    (.vector (twiddleFormat.width + twiddleFormat.width) .bit)
    (Bool.toNat pipeline.registerInputs) twiddleInputExecution
  have productContract :=
    PipelinedSignedComplexMultiply.contract_of_execution
      dataFormat.width twiddleFormat.width twiddleFormat.fractionalBits
      pipeline.complexMultiply productExecution
  have productDelayContract := OptionalShiftRegister.contract_of_execution
    (.vector (dataFormat.width + dataFormat.width) .bit)
    (Bool.toNat pipeline.registerProduct) productDelayExecution
  have aAlignContract := OptionalShiftRegister.contract_of_execution
    (.vector (dataFormat.width + dataFormat.width) .bit)
    (pipeline.complexMultiply.latency +
      Bool.toNat pipeline.registerProduct) aAlignExecution
  have upperOutputContract := OptionalShiftRegister.contract_of_execution
    (.vector
      (outputComponentWidth dataFormat + outputComponentWidth dataFormat) .bit)
    (Bool.toNat pipeline.registerOutputs) upperOutputExecution
  have lowerOutputContract := OptionalShiftRegister.contract_of_execution
    (.vector
      (outputComponentWidth dataFormat + outputComponentWidth dataFormat) .bit)
    (Bool.toNat pipeline.registerOutputs) lowerOutputExecution

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
    have inputStageInHierarchy :
        t + Bool.toNat pipeline.registerInputs < hierarchy.length := by
      rw [hierarchyLength, ← execution.length_eq]
      unfold Pipeline.latency at outputInTrace
      unfold PipelinedSignedComplexMultiply.Pipeline.latency at outputInTrace
      omega
    have productStageInHierarchy :
        t + Bool.toNat pipeline.registerInputs +
            pipeline.complexMultiply.latency < hierarchy.length := by
      rw [hierarchyLength, ← execution.length_eq]
      unfold Pipeline.latency at outputInTrace
      omega
    have addStageInHierarchy :
        t + Bool.toNat pipeline.registerInputs +
              pipeline.complexMultiply.latency +
            Bool.toNat pipeline.registerProduct < hierarchy.length := by
      rw [hierarchyLength, ← execution.length_eq]
      unfold Pipeline.latency at outputInTrace
      omega
    have finalInHierarchy : t + pipeline.latency < hierarchy.length := by
      rw [hierarchyLength, ← execution.length_eq]
      exact outputInTrace

    let sourceStep := hierarchy.get ⟨t, sourceInHierarchy⟩
    let inputStep := hierarchy.get
      ⟨t + Bool.toNat pipeline.registerInputs, inputStageInHierarchy⟩
    let productStep := hierarchy.get
      ⟨t + Bool.toNat pipeline.registerInputs +
        pipeline.complexMultiply.latency, productStageInHierarchy⟩
    let addStep := hierarchy.get
      ⟨t + Bool.toNat pipeline.registerInputs +
          pipeline.complexMultiply.latency +
        Bool.toNat pipeline.registerProduct, addStageInHierarchy⟩
    let finalStep := hierarchy.get
      ⟨t + pipeline.latency, finalInHierarchy⟩

    have sourceSolution := observed.solution_at t sourceInHierarchy
    have inputSolution := observed.solution_at
      (t + Bool.toNat pipeline.registerInputs) inputStageInHierarchy
    have productSolution := observed.solution_at
      (t + Bool.toNat pipeline.registerInputs +
        pipeline.complexMultiply.latency) productStageInHierarchy
    have addSolution := observed.solution_at
      (t + Bool.toNat pipeline.registerInputs +
          pipeline.complexMultiply.latency +
        Bool.toNat pipeline.registerProduct) addStageInHierarchy
    have finalSolution := observed.solution_at
      (t + pipeline.latency) finalInHierarchy
    have sourceAt := observed.input_at t sourceInHierarchy inputInTrace
    change sourceStep.inputs = inputs.get ⟨t, inputInTrace⟩ at sourceAt

    have aInputAt := FixedLatency.relation_at_of_trace
      aInputExecution aInputContract t
      (by simpa using sourceInHierarchy)
      (by simpa using inputStageInHierarchy)
    have bInputAt := FixedLatency.relation_at_of_trace
      bInputExecution bInputContract t
      (by simpa using sourceInHierarchy)
      (by simpa using inputStageInHierarchy)
    have twiddleInputAt := FixedLatency.relation_at_of_trace
      twiddleInputExecution twiddleInputContract t
      (by simpa using sourceInHierarchy)
      (by simpa using inputStageInHierarchy)
    simp only [List.get_eq_getElem, List.getElem_map] at aInputAt bInputAt twiddleInputAt
    change (inputStep.children .aInputDelay).outputs .output =
      (sourceStep.children .aInputDelay).inputs .input at aInputAt
    change (inputStep.children .bInputDelay).outputs .output =
      (sourceStep.children .bInputDelay).inputs .input at bInputAt
    change (inputStep.children .twiddleInputDelay).outputs .output =
      (sourceStep.children .twiddleInputDelay).inputs .input at twiddleInputAt
    have aRootInput := ModuleStructure.child_input sourceSolution
      (.aInputDelay) (.input)
    have bRootInput := ModuleStructure.child_input sourceSolution
      (.bInputDelay) (.input)
    have twiddleRootInput := ModuleStructure.child_input sourceSolution
      (.twiddleInputDelay) (.input)
    change (sourceStep.children .aInputDelay).inputs .input =
      sourceStep.inputs .a at aRootInput
    change (sourceStep.children .bInputDelay).inputs .input =
      sourceStep.inputs .b at bRootInput
    change (sourceStep.children .twiddleInputDelay).inputs .input =
      sourceStep.inputs .twiddle at twiddleRootInput
    rw [aRootInput, sourceAt] at aInputAt
    rw [bRootInput, sourceAt] at bInputAt
    rw [twiddleRootInput, sourceAt] at twiddleInputAt

    have productOutputAt := FixedLatency.relation_at_of_trace
      productExecution productContract
      (t + Bool.toNat pipeline.registerInputs)
      (by simpa using inputStageInHierarchy)
      (by simpa [Nat.add_assoc] using productStageInHierarchy)
    simp only [List.get_eq_getElem, List.getElem_map] at productOutputAt
    change (productStep.children .product).outputs .resultReal =
          PipelinedSignedComplexMultiply.realResultValue
            dataFormat.width twiddleFormat.width
            twiddleFormat.fractionalBits
            ((inputStep.children .product).inputs .leftReal)
            ((inputStep.children .product).inputs .leftImag)
            ((inputStep.children .product).inputs .rightReal)
            ((inputStep.children .product).inputs .rightImag) ∧
      (productStep.children .product).outputs .resultImag =
          PipelinedSignedComplexMultiply.imagResultValue
            dataFormat.width twiddleFormat.width
            twiddleFormat.fractionalBits
            ((inputStep.children .product).inputs .leftReal)
            ((inputStep.children .product).inputs .leftImag)
            ((inputStep.children .product).inputs .rightReal)
            ((inputStep.children .product).inputs .rightImag)
      at productOutputAt
    have productInputs := productInputs_of_solution
      dataFormat.width dataFormat.fractionalBits
      twiddleFormat.width twiddleFormat.fractionalBits
      pipeline.registerInputs pipeline.complexMultiply.multiplierLatency
      pipeline.complexMultiply.registerBeforeRounding
      pipeline.registerProduct pipeline.registerOutputs inputSolution
    rw [productInputs.1, productInputs.2.1,
      productInputs.2.2.1, productInputs.2.2.2,
      bInputAt, twiddleInputAt] at productOutputAt
    have packedProduct :
        packProductOutputs dataFormat twiddleFormat
          ((productStep.children .product).outputs .resultReal)
          ((productStep.children .product).outputs .resultImag) =
        productBoundaryCircuitValue dataFormat twiddleFormat
          (highComponent dataFormat.width
            (inputs.get ⟨t, inputInTrace⟩ .b))
          (lowComponent dataFormat.width
            (inputs.get ⟨t, inputInTrace⟩ .b))
          (highComponent twiddleFormat.width
            (inputs.get ⟨t, inputInTrace⟩ .twiddle))
          (lowComponent twiddleFormat.width
            (inputs.get ⟨t, inputInTrace⟩ .twiddle)) := by
      unfold productBoundaryCircuitValue
      rw [productOutputAt.1, productOutputAt.2]

    have productDelayAt := FixedLatency.relation_at_of_trace
      productDelayExecution productDelayContract
      (t + Bool.toNat pipeline.registerInputs +
        pipeline.complexMultiply.latency)
      (by simpa using productStageInHierarchy)
      (by simpa [Nat.add_assoc] using addStageInHierarchy)
    simp only [List.get_eq_getElem, List.getElem_map] at productDelayAt
    change (addStep.children .productDelay).outputs .output =
      (productStep.children .productDelay).inputs .input at productDelayAt
    have productDelayInput := productDelayInput_of_solution
      dataFormat.width dataFormat.fractionalBits
      twiddleFormat.width twiddleFormat.fractionalBits
      pipeline.registerInputs pipeline.complexMultiply.multiplierLatency
      pipeline.complexMultiply.registerBeforeRounding
      pipeline.registerProduct pipeline.registerOutputs productSolution
    rw [productDelayInput, packedProduct] at productDelayAt
    have fixedProduct := productBoundaryCircuitValue_eq_fixedMultiply
      dataFormat twiddleFormat carrier
      (highComponent dataFormat.width
        (inputs.get ⟨t, inputInTrace⟩ .b))
      (lowComponent dataFormat.width
        (inputs.get ⟨t, inputInTrace⟩ .b))
      (highComponent twiddleFormat.width
        (inputs.get ⟨t, inputInTrace⟩ .twiddle))
      (lowComponent twiddleFormat.width
        (inputs.get ⟨t, inputInTrace⟩ .twiddle))
    have productAtAdd :
        (addStep.children .productDelay).outputs .output =
          encodeComplex dataFormat.width
            (HTFFT.Butterfly.Fixed.multiply
              (fixedConfig dataFormat twiddleFormat)
              (decodeComplex dataFormat.width
                (inputs.get ⟨t, inputInTrace⟩ .b))
              (decodeComplex twiddleFormat.width
                (inputs.get ⟨t, inputInTrace⟩ .twiddle))) := by
      rw [productDelayAt, fixedProduct]
      rfl

    have aAlignOutputInHierarchy :
        (t + Bool.toNat pipeline.registerInputs) +
            (pipeline.complexMultiply.latency +
              Bool.toNat pipeline.registerProduct) < hierarchy.length := by
      omega
    have aAlignAt := FixedLatency.relation_at_of_trace
      aAlignExecution aAlignContract
      (t + Bool.toNat pipeline.registerInputs)
      (by simpa using inputStageInHierarchy)
      (by simpa using aAlignOutputInHierarchy)
    simp only [List.get_eq_getElem, List.getElem_map] at aAlignAt
    change
      ((hierarchy.get ⟨(t + Bool.toNat pipeline.registerInputs) +
          (pipeline.complexMultiply.latency +
            Bool.toNat pipeline.registerProduct),
          aAlignOutputInHierarchy⟩).children .aAlignDelay).outputs .output =
        ((hierarchy.get ⟨t + Bool.toNat pipeline.registerInputs,
          inputStageInHierarchy⟩).children .aAlignDelay).inputs .input
      at aAlignAt
    have aAlignAtNormalized :
        (addStep.children .aAlignDelay).outputs .output =
          (inputStep.children .aAlignDelay).inputs .input := by
      simpa [addStep, inputStep, Nat.add_assoc] using aAlignAt
    have aAlignInput := aAlignInput_of_solution
      dataFormat.width dataFormat.fractionalBits
      twiddleFormat.width twiddleFormat.fractionalBits
      pipeline.registerInputs pipeline.complexMultiply.multiplierLatency
      pipeline.complexMultiply.registerBeforeRounding
      pipeline.registerProduct pipeline.registerOutputs inputSolution
    rw [aAlignInput, aInputAt] at aAlignAtNormalized

    have outputInputs := outputDelayInputs_of_solution
      dataFormat.width dataFormat.fractionalBits
      twiddleFormat.width twiddleFormat.fractionalBits
      pipeline.registerInputs pipeline.complexMultiply.multiplierLatency
      pipeline.complexMultiply.registerBeforeRounding
      pipeline.registerProduct pipeline.registerOutputs addSolution
    rw [aAlignAtNormalized, productAtAdd] at outputInputs
    have arithmetic := addSubCircuitValues_eq_fixedButterfly
      dataFormat twiddleFormat
      (inputs.get ⟨t, inputInTrace⟩ .a)
      (inputs.get ⟨t, inputInTrace⟩ .b)
      (inputs.get ⟨t, inputInTrace⟩ .twiddle)
    rw [arithmetic.1, arithmetic.2] at outputInputs

    have outputDelayInHierarchy :
        (t + Bool.toNat pipeline.registerInputs +
              pipeline.complexMultiply.latency +
            Bool.toNat pipeline.registerProduct) +
          Bool.toNat pipeline.registerOutputs < hierarchy.length := by
      simpa [Pipeline.latency, Nat.add_assoc] using finalInHierarchy
    have upperOutputAt := FixedLatency.relation_at_of_trace
      upperOutputExecution upperOutputContract
      (t + Bool.toNat pipeline.registerInputs +
          pipeline.complexMultiply.latency +
        Bool.toNat pipeline.registerProduct)
      (by simpa using addStageInHierarchy)
      (by simpa using outputDelayInHierarchy)
    have lowerOutputAt := FixedLatency.relation_at_of_trace
      lowerOutputExecution lowerOutputContract
      (t + Bool.toNat pipeline.registerInputs +
          pipeline.complexMultiply.latency +
        Bool.toNat pipeline.registerProduct)
      (by simpa using addStageInHierarchy)
      (by simpa using outputDelayInHierarchy)
    simp only [List.get_eq_getElem, List.getElem_map] at upperOutputAt lowerOutputAt
    change
      ((hierarchy.get ⟨
        (t + Bool.toNat pipeline.registerInputs +
              pipeline.complexMultiply.latency +
            Bool.toNat pipeline.registerProduct) +
          Bool.toNat pipeline.registerOutputs,
        outputDelayInHierarchy⟩).children .upperOutputDelay).outputs .output =
      ((hierarchy.get ⟨
        t + Bool.toNat pipeline.registerInputs +
            pipeline.complexMultiply.latency +
          Bool.toNat pipeline.registerProduct,
        addStageInHierarchy⟩).children .upperOutputDelay).inputs .input
      at upperOutputAt
    change
      ((hierarchy.get ⟨
        (t + Bool.toNat pipeline.registerInputs +
              pipeline.complexMultiply.latency +
            Bool.toNat pipeline.registerProduct) +
          Bool.toNat pipeline.registerOutputs,
        outputDelayInHierarchy⟩).children .lowerOutputDelay).outputs .output =
      ((hierarchy.get ⟨
        t + Bool.toNat pipeline.registerInputs +
            pipeline.complexMultiply.latency +
          Bool.toNat pipeline.registerProduct,
        addStageInHierarchy⟩).children .lowerOutputDelay).inputs .input
      at lowerOutputAt
    have upperOutputAtNormalized :
        (finalStep.children .upperOutputDelay).outputs .output =
          (addStep.children .upperOutputDelay).inputs .input := by
      simpa [finalStep, addStep, Pipeline.latency, Nat.add_assoc] using
        upperOutputAt
    have lowerOutputAtNormalized :
        (finalStep.children .lowerOutputDelay).outputs .output =
          (addStep.children .lowerOutputDelay).inputs .input := by
      simpa [finalStep, addStep, Pipeline.latency, Nat.add_assoc] using
        lowerOutputAt
    rw [outputInputs.1] at upperOutputAtNormalized
    rw [outputInputs.2] at lowerOutputAtNormalized

    have parentOutputs := parentOutputs_of_solution
      dataFormat.width dataFormat.fractionalBits
      twiddleFormat.width twiddleFormat.fractionalBits
      pipeline.registerInputs pipeline.complexMultiply.multiplierLatency
      pipeline.complexMultiply.registerBeforeRounding
      pipeline.registerProduct pipeline.registerOutputs finalSolution
    have outputAt := observed.output_at rootOutputs
      (t + pipeline.latency) finalInHierarchy outputInTrace
    change finalStep.outputs =
      outputs.get ⟨t + pipeline.latency, outputInTrace⟩ at outputAt
    have upperAt := congrFun outputAt .upper
    have lowerAt := congrFun outputAt .lower
    constructor
    · rw [← upperAt, parentOutputs.1, upperOutputAtNormalized]
    · rw [← lowerAt, parentOutputs.2, lowerOutputAtNormalized]

end HTFFT.Silean.PipelinedFixedButterfly.Internal
