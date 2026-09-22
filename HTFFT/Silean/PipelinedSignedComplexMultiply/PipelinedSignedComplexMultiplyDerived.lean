import HTFFT.Silean.PipelinedSignedComplexMultiply.Internal.PipelinedSignedComplexMultiplyVerification

/-! Public placement and correctness declarations for the structural
pipelined signed complex multiplier. -/

namespace HTFFT.Silean.PipelinedSignedComplexMultiply

open _root_.Silean
open _root_.Silean.Authoring.CircuitDescription

/-- Place the structural four-product complex multiplier. -/
noncomputable def place
    (discardedWidth : Nat) (pipeline : Pipeline)
    (leftReal leftImag : Net (.vector leftWidth .bit))
    (rightReal rightImag : Net (.vector rightWidth .bit)) :
    Builder (ports.OutputNets leftWidth rightWidth discardedWidth) :=
  ports.placeIndexed leftWidth rightWidth discardedWidth
    "pipelined_signed_complex_multiply"
    (moduleStructure leftWidth rightWidth discardedWidth
      pipeline.multiplierLatency pipeline.registerBeforeRounding)
    (naming leftWidth rightWidth discardedWidth
      pipeline.multiplierLatency pipeline.registerBeforeRounding)
    leftReal leftImag rightReal rightImag

attribute [circuit_description] place

/-- The complete hierarchy has exactly one structural solution for every
input and physical state. -/
theorem structuralCertification
    (leftWidth rightWidth discardedWidth : Nat) (pipeline : Pipeline) :
    ModuleStructuralCertification
      (moduleStructure leftWidth rightWidth discardedWidth
        pipeline.multiplierLatency pipeline.registerBeforeRounding) :=
  Internal.structuralCertification
    leftWidth rightWidth discardedWidth pipeline.multiplierLatency
      pipeline.registerBeforeRounding

/-- Every structural execution satisfies the all-time latency contract. -/
theorem contract_of_execution
    (leftWidth rightWidth discardedWidth : Nat) (pipeline : Pipeline)
    {initialState finalState :
      (moduleStructure leftWidth rightWidth discardedWidth
        pipeline.multiplierLatency pipeline.registerBeforeRounding).State}
    {inputs : List (ports leftWidth rightWidth discardedWidth).inputs.Values}
    {outputs : List (ports leftWidth rightWidth discardedWidth).outputs.Values}
    (execution :
      (moduleStructure leftWidth rightWidth discardedWidth
        pipeline.multiplierLatency pipeline.registerBeforeRounding).Executes
          initialState inputs outputs finalState) :
    contract leftWidth rightWidth discardedWidth pipeline
      execution.toBoundaryTrace :=
  Internal.contract_of_execution
    leftWidth rightWidth discardedWidth pipeline execution

end HTFFT.Silean.PipelinedSignedComplexMultiply
