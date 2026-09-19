import PicoRV.Memory.MemoryBasicUpdates
import PicoRV.Memory.MemoryProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.MuxTheorems
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems

namespace PicoRV.Memory.PrefetchedUpdate

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  inputsFields := Silean.Modules.NamedTupleSplitter.certification MemoryInputs.signalMap,
  updatedFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  idleState := Silean.Modules.Constant.certification (.vector 2 .bit) (stateOfNat 0),
  phase := Silean.Modules.Mux.certification (.vector 2 .bit),
  result := Silean.Modules.NamedTupleCombiner.certification stateMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    {.inputsFields, .updatedFields} => Silean.Modules.NamedTupleSplitter.Rule.apply,
    .idleState => Silean.Primitives.ConstantRule.apply,
    .phase => Silean.Modules.Mux.Rule.select,
    .result => Silean.Modules.NamedTupleCombiner.Rule.apply]
  state := []

def structuralResult (memoryInputs : Inputs) (updated : stateMap.Values) :
    stateMap.Values
  | .mem_state => bif memoryInputs.mem_do_rinst
      then stateOfNat 0 else updated .mem_state
  | field => updated field

theorem structuralResult_eq_prefetchedNextState (memoryInputs : Inputs)
    (updated : stateMap.Values) :
    structuralResult memoryInputs updated = prefetchedNextState memoryInputs updated := by
  cases instruction : memoryInputs.mem_do_rinst <;> funext field <;> cases field <;>
    simp [structuralResult, prefetchedNextState, instruction, Silean.SignalMap.set]

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
  let updated := stateMap.unpack (inputs .updated)
  have inputsFieldsValue : hierStep.childOutputs .inputsFields =
      MemoryInputs.signalMap.unpack (inputs .inputs) := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      MemoryInputs.signalMap _ _ _).mp
      ((childMatch .inputsFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    simpa [ProofSupport.splitValue_eq_unpack] using equation
  have updatedFieldsValue : hierStep.childOutputs .updatedFields = updated := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .updatedFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    simpa [ProofSupport.splitValue_eq_unpack, updated] using equation
  have instructionValue : hierStep.childOutputs .inputsFields .mem_do_rinst =
      memoryInputs.mem_do_rinst := by rw [inputsFieldsValue]; rfl
  have idleValue := (Silean.Modules.Constant.outputRule_holds_iff
    (.vector 2 .bit) (stateOfNat 0) _ _ _).mp
    ((childMatch .idleState).ruleHolds Silean.Primitives.ConstantRule.apply)
  have phaseValue : hierStep.childOutputs .phase .result =
      bif memoryInputs.mem_do_rinst then stateOfNat 0 else updated .mem_state := by
    have equation := Silean.Modules.Mux.result_of_allowed (.vector 2 .bit)
      (childMatch .phase).allowed
    normalize_child_hyp equation unfolding wiring, context
    rw [instructionValue, updatedFieldsValue, idleValue] at equation
    exact equation

  have resultInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .result = structuralResult memoryInputs updated := by
    funext field
    cases field
    · change hierStep.childOutputs .phase .result = _; exact phaseValue
    · change hierStep.childOutputs .updatedFields .mem_valid = _
      exact congrFun updatedFieldsValue .mem_valid
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
      stateMap.pack (structuralResult memoryInputs updated) := by
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
    rw [resultValue, structuralResult_eq_prefetchedNextState]
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

end PicoRV.Memory.PrefetchedUpdate
