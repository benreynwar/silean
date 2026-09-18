import PicoRV.Memory.MemoryBasicUpdates
import PicoRV.Memory.MemoryProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.Internal.MuxVerification
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems
import Silean.Primitives.And

namespace PicoRV.Memory.WriteUpdate

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  inputsFields := Silean.Modules.NamedTupleSplitter.certification MemoryInputs.signalMap,
  currentFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  updatedFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  transfer := Silean.Primitives.andCertified.certification,
  falseBit := Silean.Modules.Constant.certification .bit false,
  idleState := Silean.Modules.Constant.certification (.vector 2 .bit) (stateOfNat 0),
  valid := Silean.Modules.Mux.certification .bit,
  phase := Silean.Modules.Mux.certification (.vector 2 .bit),
  result := Silean.Modules.NamedTupleCombiner.certification stateMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    {.inputsFields, .currentFields, .updatedFields} =>
      Silean.Modules.NamedTupleSplitter.Rule.apply,
    .transfer => Silean.Primitives.AndRule.apply,
    {.falseBit, .idleState} => Silean.Primitives.ConstantRule.apply,
    {.valid, .phase} => Silean.Modules.Mux.Rule.select,
    .result => Silean.Modules.NamedTupleCombiner.Rule.apply]
  state := []

def structuralResult (memoryInputs : Inputs) (current updated : stateMap.Values) :
    stateMap.Values
  | .mem_state => bif memXfer memoryInputs current
      then stateOfNat 0 else updated .mem_state
  | .mem_valid => bif memXfer memoryInputs current
      then false else updated .mem_valid
  | field => updated field

theorem structuralResult_eq_writeNextState (memoryInputs : Inputs)
    (current updated : stateMap.Values) :
    structuralResult memoryInputs current updated =
      writeNextState memoryInputs current updated := by
  cases valid : current .mem_valid <;> cases ready : memoryInputs.mem_ready <;>
    funext field <;> cases field <;>
    simp [structuralResult, writeNextState, memXfer, memXferFrom, valid, ready,
      Silean.SignalMap.set]

section Certification

variable (layerChildren : ChildStructures body childContracts)

private abbrev certificationStructure :=
  Silean.Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements :
    Silean.Contracts.Cycle.ImplementsSolutions (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  let inputs := hierStep.inputs
  have childMatch (child : Instance) :=
    (childSolutionMatchesCoveredContract layerChildren hierStep
      satisfies child).choose_spec

  let memoryInputs := Inputs.unpack (inputs .inputs)
  let current := stateMap.unpack (inputs .current)
  let updated := stateMap.unpack (inputs .updated)
  have inputsFieldsValue : hierStep.childOutputs .inputsFields =
      MemoryInputs.signalMap.unpack (inputs .inputs) := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      MemoryInputs.signalMap _ _ _).mp
      ((childMatch .inputsFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    simpa [ProofSupport.splitValue_eq_unpack] using equation
  have currentFieldsValue : hierStep.childOutputs .currentFields = current := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .currentFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    simpa [ProofSupport.splitValue_eq_unpack, current] using equation
  have updatedFieldsValue : hierStep.childOutputs .updatedFields = updated := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .updatedFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    simpa [ProofSupport.splitValue_eq_unpack, updated] using equation
  have readyValue : hierStep.childOutputs .inputsFields .mem_ready =
      memoryInputs.mem_ready := by rw [inputsFieldsValue]; rfl
  have transferValue : hierStep.childOutputs .transfer .output =
      memXfer memoryInputs current := by
    have equation := (Silean.Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .transfer).ruleHolds Silean.Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [currentFieldsValue, readyValue] at equation
    simpa [memXfer, memXferFrom] using equation
  have falseValue := (Silean.Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    ((childMatch .falseBit).ruleHolds Silean.Primitives.ConstantRule.apply)
  have idleValue := (Silean.Modules.Constant.outputRule_holds_iff
    (.vector 2 .bit) (stateOfNat 0) _ _ _).mp
    ((childMatch .idleState).ruleHolds Silean.Primitives.ConstantRule.apply)
  have validValue : hierStep.childOutputs .valid .result =
      bif memXfer memoryInputs current then false else updated .mem_valid := by
    have equation := Silean.Modules.Mux.result_of_allowed .bit
      (childMatch .valid).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [transferValue, updatedFieldsValue, falseValue] at equation
    exact equation
  have phaseValue : hierStep.childOutputs .phase .result =
      bif memXfer memoryInputs current then stateOfNat 0 else updated .mem_state := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 2 .bit)
      (childMatch .phase).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [transferValue, updatedFieldsValue, idleValue] at equation
    exact equation

  have resultInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .result = structuralResult memoryInputs current updated := by
    funext field
    cases field
    · change hierStep.childOutputs .phase .result = _; exact phaseValue
    · change hierStep.childOutputs .valid .result = _; exact validValue
    · change hierStep.childOutputs .updatedFields .mem_instr = _
      exact congrFun updatedFieldsValue .mem_instr
    · change hierStep.childOutputs .updatedFields .mem_addr = _
      exact congrFun updatedFieldsValue .mem_addr
    · change hierStep.childOutputs .updatedFields .mem_wdata = _
      exact congrFun updatedFieldsValue .mem_wdata
    · change hierStep.childOutputs .updatedFields .mem_wstrb = _
      exact congrFun updatedFieldsValue .mem_wstrb
    · change hierStep.childOutputs .updatedFields .mem_rdata_q = _
      exact congrFun updatedFieldsValue .mem_rdata_q
  have resultValue : hierStep.childOutputs .result .value =
      stateMap.pack (structuralResult memoryInputs current updated) := by
    have equation := (Silean.Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .result).ruleHolds Silean.Modules.NamedTupleCombiner.Rule.apply)
    rw [resultInputs] at equation
    rw [equation, Silean.Modules.NamedTupleCombiner.combinedValue_eq_pack]

  refine ⟨Silean.SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [StateUpdate.outputRule_holds_iff]
    dsimp only
    rw [show hierStep.outputs .state = hierStep.childOutputs .result .value by
      exact satisfies.1 .state]
    rw [resultValue, structuralResult_eq_writeNextState]
    rfl
  · rfl

end Certification

module_cycle_certification certification for moduleStructure via body
    with childContracts implementing cycleContract where
  schedules := derivedRuleSchedules,
  structuralChildren := structuralChildren,
  certifiedChildren := certifiedChildren,
  structuresMatch := certifiedChildren_moduleStructure,
  stateCorresponds := stateCorresponds,
  stateCoverage := fun _ _ => ⟨Silean.SignalMap.emptyValues, trivial⟩,
  implements := implements

end PicoRV.Memory.WriteUpdate
