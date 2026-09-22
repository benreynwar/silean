import HTFFT.Silean.PipelinedFixedButterfly.Internal.PipelinedFixedButterflyVerification

/-! Public placement and correctness declarations for the structural
pipelined fixed-point butterfly. -/

namespace HTFFT.Silean.PipelinedFixedButterfly

open _root_.Silean
open _root_.Silean.Authoring.CircuitDescription

/-- Place the structural fixed-point butterfly. -/
noncomputable def place
    (dataFormat twiddleFormat : HTFFT.FixedPoint.Format)
    (pipeline : Pipeline)
    (a b : Net (.vector (dataFormat.width + dataFormat.width) .bit))
    (twiddle : Net
      (.vector (twiddleFormat.width + twiddleFormat.width) .bit)) :
    Builder (ports.OutputNets dataFormat twiddleFormat) :=
  ports.placeIndexed dataFormat twiddleFormat
    "pipelined_fixed_butterfly"
    (moduleStructure dataFormat.width dataFormat.fractionalBits
      twiddleFormat.width twiddleFormat.fractionalBits
      pipeline.registerInputs pipeline.complexMultiply.multiplierLatency
      pipeline.complexMultiply.registerBeforeRounding
      pipeline.registerProduct pipeline.registerOutputs)
    (naming dataFormat.width dataFormat.fractionalBits
      twiddleFormat.width twiddleFormat.fractionalBits
      pipeline.registerInputs pipeline.complexMultiply.multiplierLatency
      pipeline.complexMultiply.registerBeforeRounding
      pipeline.registerProduct pipeline.registerOutputs)
    a b twiddle

attribute [circuit_description] place

/-- The complete hierarchy has exactly one structural solution for every
input and physical state. -/
theorem structuralCertification
    (dataFormat twiddleFormat : HTFFT.FixedPoint.Format)
    (pipeline : Pipeline) :
    ModuleStructuralCertification
      (moduleStructure dataFormat.width dataFormat.fractionalBits
        twiddleFormat.width twiddleFormat.fractionalBits
        pipeline.registerInputs pipeline.complexMultiply.multiplierLatency
        pipeline.complexMultiply.registerBeforeRounding
        pipeline.registerProduct pipeline.registerOutputs) :=
  Internal.structuralCertification
    dataFormat.width dataFormat.fractionalBits
    twiddleFormat.width twiddleFormat.fractionalBits
    pipeline.registerInputs pipeline.complexMultiply.multiplierLatency
    pipeline.complexMultiply.registerBeforeRounding
    pipeline.registerProduct pipeline.registerOutputs

/-- Every structural execution satisfies the all-time fixed-latency contract.
The carrier condition is static: the generic complex multiplier must expose
at least the requested data-width product boundary. -/
theorem contract_of_execution
    (dataFormat twiddleFormat : HTFFT.FixedPoint.Format)
    (pipeline : Pipeline)
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
    contract dataFormat twiddleFormat pipeline execution.toBoundaryTrace :=
  Internal.contract_of_execution dataFormat twiddleFormat pipeline carrier
    execution

end HTFFT.Silean.PipelinedFixedButterfly
