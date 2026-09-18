import Silean.Examples.PicoRV.Memory.MemoryBasicUpdates
import Silean.Examples.PicoRV.Memory.MemoryProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Mux.Internal.MuxVerification
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems
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
    Contracts.Cycle.ImplementsSolutions (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  let inputs := hierStep.inputs
  have childMatch (child : Instance) :=
    (childSolutionMatchesCoveredContract layerChildren hierStep
      satisfies child).choose_spec

  let memoryInputs := Inputs.unpack (inputs .inputs)
  let current := stateMap.unpack (inputs .current)
  have inputsFieldsValue : hierStep.childOutputs .inputsFields =
      MemoryInputs.signalMap.unpack (inputs .inputs) := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      MemoryInputs.signalMap _ _ _).mp
      ((childMatch .inputsFields).ruleHolds Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    simpa [ProofSupport.splitValue_eq_unpack] using equation
  have currentFieldsValue : hierStep.childOutputs .currentFields = current := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .currentFields).ruleHolds Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    simpa [ProofSupport.splitValue_eq_unpack, current] using equation
  have readyValue : hierStep.childOutputs .inputsFields .mem_ready =
      memoryInputs.mem_ready := by rw [inputsFieldsValue]; rfl
  have rdataValue : hierStep.childOutputs .inputsFields .mem_rdata =
      memoryInputs.mem_rdata := by rw [inputsFieldsValue]; rfl
  have transferValue : hierStep.childOutputs .transfer .output =
      (current .mem_valid && memoryInputs.mem_ready) := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .transfer).ruleHolds Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [currentFieldsValue, readyValue] at equation
    exact equation
  have responseValue : hierStep.childOutputs .response .result =
      bif (current .mem_valid && memoryInputs.mem_ready)
        then memoryInputs.mem_rdata else current .mem_rdata_q := by
    have equation := Modules.Mux.result_of_allowed (.vector 32 .bit)
      (childMatch .response).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [transferValue, currentFieldsValue, rdataValue] at equation
    exact equation

  let resultState := structuralResult memoryInputs current
  have resultInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .result = resultState := by
    funext field
    cases field
    · change hierStep.childOutputs .currentFields .mem_state = _
      exact congrFun currentFieldsValue .mem_state
    · change hierStep.childOutputs .currentFields .mem_valid = _
      exact congrFun currentFieldsValue .mem_valid
    · change hierStep.childOutputs .currentFields .mem_instr = _
      exact congrFun currentFieldsValue .mem_instr
    · change hierStep.childOutputs .currentFields .mem_addr = _
      exact congrFun currentFieldsValue .mem_addr
    · change hierStep.childOutputs .currentFields .mem_wdata = _
      exact congrFun currentFieldsValue .mem_wdata
    · change hierStep.childOutputs .currentFields .mem_wstrb = _
      exact congrFun currentFieldsValue .mem_wstrb
    · change hierStep.childOutputs .response .result = _; exact responseValue
  have resultValue : hierStep.childOutputs .result .value =
      stateMap.pack resultState := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .result).ruleHolds Modules.NamedTupleCombiner.Rule.apply)
    rw [resultInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    dsimp only
    rw [show hierStep.outputs .state = hierStep.childOutputs .result .value by
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

end Silean.Examples.PicoRV.Memory.ResponseCapture
