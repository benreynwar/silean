import Silean.Modules.PipelinedSignedMultiply.Internal.PipelinedSignedMultiplyVerification

/-! Public declarations backed by the structural output-register pipeline. -/

namespace Silean.Modules.PipelinedSignedMultiply

open Silean
open Authoring.CircuitDescription

/-- Place a signed multiplier followed by a statically sized output-register
chain. -/
noncomputable def place
    (latency : Nat)
    (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) :
    Builder (Net (.vector (leftWidth + rightWidth) .bit)) := do
  let outputs ← ports.placeIndexed leftWidth rightWidth
    "pipelined_signed_multiply"
    (moduleStructure leftWidth rightWidth latency)
    (naming leftWidth rightWidth latency) left right
  pure outputs.result

attribute [circuit_description] place

/-- The hierarchy has exactly one structural solution for every input and
physical state. -/
theorem structuralCertification (leftWidth rightWidth latency : Nat) :
    ModuleStructuralCertification
      (moduleStructure leftWidth rightWidth latency) :=
  Internal.structuralCertification leftWidth rightWidth latency

/-- Every structural execution satisfies the all-time latency contract. -/
theorem contract_of_execution (leftWidth rightWidth latency : Nat)
    {initialState finalState :
      (moduleStructure leftWidth rightWidth latency).State}
    {inputs : List (ports leftWidth rightWidth).inputs.Values}
    {outputs : List (ports leftWidth rightWidth).outputs.Values}
    (execution : (moduleStructure leftWidth rightWidth latency).Executes
      initialState inputs outputs finalState) :
    contract leftWidth rightWidth latency execution.toBoundaryTrace :=
  Internal.contract_of_execution leftWidth rightWidth latency execution

/-- At every valid delayed trace position, decoding the result gives exact
mathematical signed multiplication. -/
theorem result_toInt_of_execution (leftWidth rightWidth latency : Nat)
    {initialState finalState :
      (moduleStructure leftWidth rightWidth latency).State}
    {inputs : List (ports leftWidth rightWidth).inputs.Values}
    {outputs : List (ports leftWidth rightWidth).outputs.Values}
    (execution : (moduleStructure leftWidth rightWidth latency).Executes
      initialState inputs outputs finalState)
    (t : Nat) (inputInTrace : t < inputs.length)
    (outputInTrace : t + latency < outputs.length) :
    (BitVector.toBitVec (leftWidth + rightWidth)
      (outputs.get ⟨t + latency, outputInTrace⟩ .result)).toInt =
      (BitVector.toBitVec leftWidth
        (inputs.get ⟨t, inputInTrace⟩ .left)).toInt *
      (BitVector.toBitVec rightWidth
        (inputs.get ⟨t, inputInTrace⟩ .right)).toInt := by
  have result := FixedLatency.relation_at_of_trace execution
    (contract_of_execution leftWidth rightWidth latency execution)
    t inputInTrace outputInTrace
  rw [result]
  exact SignedMultiply.resultValue_toInt leftWidth rightWidth
    (inputs.get ⟨t, inputInTrace⟩ .left)
    (inputs.get ⟨t, inputInTrace⟩ .right)

end Silean.Modules.PipelinedSignedMultiply
