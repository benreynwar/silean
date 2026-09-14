import Silean.Examples.PicoRV.Memory.MemoryBasicUpdates
import Silean.Examples.PicoRV.Memory.MemoryProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Mux.MuxCertified
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified
import Silean.Primitives.And

namespace Silean.Examples.PicoRV.Memory.ResponseCapture

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  inputsFields := Modules.NamedTupleSplitter.certification MemoryInputs.signalMap,
  currentFields := Modules.NamedTupleSplitter.certification stateMap,
  transfer := Primitives.andCertified.certification,
  response := Modules.Mux.certification (.vector 32 .bit),
  result := Modules.NamedTupleCombiner.certification stateMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    {.inputsFields, .currentFields} => Modules.NamedTupleSplitter.Rule.apply,
    .transfer => Primitives.AndRule.apply,
    .response => Modules.Mux.Rule.select,
    .result => Modules.NamedTupleCombiner.Rule.apply]
  state := []

section Certification

variable (layerChildren : ChildStructures body childContracts)

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

def structuralResult (memoryInputs : Inputs) (current : stateMap.Values) :
    stateMap.Values
  | .mem_rdata_q => bif current .mem_valid && memoryInputs.mem_ready
      then memoryInputs.mem_rdata else current .mem_rdata_q
  | field => current field

theorem structuralResult_eq_responseCaptured (memoryInputs : Inputs)
    (current : stateMap.Values) :
    structuralResult memoryInputs current = responseCaptured memoryInputs current := by
  cases valid : current .mem_valid <;> cases ready : memoryInputs.mem_ready <;>
    funext field <;> cases field <;>
    simp [structuralResult, responseCaptured, memXfer, memXferFrom, valid, ready,
      SignalMap.set]

private theorem implements :
    Contracts.Cycle.Implements (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  derive_empty_state_child_matches childMatch from
    layerChildren, inputs, structuralState, proposal, satisfies

  let memoryInputs := Inputs.unpack (inputs .inputs)
  let current := stateMap.unpack (inputs .current)
  have inputsFieldsValue : (proposal.2 .inputsFields).outputs =
      MemoryInputs.signalMap.unpack (inputs .inputs) := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      MemoryInputs.signalMap _ _ _).mp
      ((childMatch .inputsFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [ProofSupport.splitValue_eq_unpack] using equation
  have currentFieldsValue : (proposal.2 .currentFields).outputs = current := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .currentFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [ProofSupport.splitValue_eq_unpack, current] using equation
  have readyValue : (proposal.2 .inputsFields).outputs .mem_ready =
      memoryInputs.mem_ready := by rw [inputsFieldsValue]; rfl
  have rdataValue : (proposal.2 .inputsFields).outputs .mem_rdata =
      memoryInputs.mem_rdata := by rw [inputsFieldsValue]; rfl
  have transferValue : (proposal.2 .transfer).outputs .output =
      (current .mem_valid && memoryInputs.mem_ready) := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .transfer).1.1 Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [currentFieldsValue, readyValue] at equation
    exact equation
  have responseValue : (proposal.2 .response).outputs .result =
      bif (current .mem_valid && memoryInputs.mem_ready)
        then memoryInputs.mem_rdata else current .mem_rdata_q := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .response).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [transferValue, currentFieldsValue, rdataValue] at equation
    exact equation

  let resultState := structuralResult memoryInputs current
  have resultInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .result = resultState := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, resultState,
        structuralResult]
    · simpa using congrFun currentFieldsValue .mem_state
    · simpa using congrFun currentFieldsValue .mem_valid
    · simpa using congrFun currentFieldsValue .mem_instr
    · simpa using congrFun currentFieldsValue .mem_addr
    · simpa using congrFun currentFieldsValue .mem_wdata
    · simpa using congrFun currentFieldsValue .mem_wstrb
    · exact responseValue
  have resultValue : (proposal.2 .result).outputs .value =
      stateMap.pack resultState := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .result).1.1 Modules.NamedTupleCombiner.Rule.apply)
    rw [resultInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    rw [show proposal.outputs .state = (proposal.2 .result).outputs .value by
      exact satisfies.1 .state]
    rw [resultValue]
    simpa [resultState, outputState, memoryInputs, current] using
      congrArg stateMap.pack
        (structuralResult_eq_responseCaptured memoryInputs current)
  · rfl

end Certification

module_cycle_certification certification for moduleStructure via body
    with childContracts implementing cycleContract where
  schedules := derivedRuleSchedules,
  structuralChildren := structuralChildren,
  certifiedChildren := certifiedChildren,
  structuresMatch := certifiedChildren_moduleStructure,
  stateCorresponds := stateCorresponds,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.Memory.ResponseCapture
