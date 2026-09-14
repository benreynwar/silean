import Silean.Examples.PicoRV.Memory.MemoryBasicUpdates
import Silean.Examples.PicoRV.Memory.MemoryProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.MuxCertified
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified
import Silean.Primitives.And
import Silean.Primitives.Or

namespace Silean.Examples.PicoRV.Memory.ReadUpdate

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  inputsFields := Modules.NamedTupleSplitter.certification MemoryInputs.signalMap,
  currentFields := Modules.NamedTupleSplitter.certification stateMap,
  updatedFields := Modules.NamedTupleSplitter.certification stateMap,
  transfer := Primitives.andCertified.certification,
  activeRead := Primitives.orCertified.certification,
  falseBit := Modules.Constant.certification .bit false,
  idleState := Modules.Constant.certification (.vector 2 .bit) (stateOfNat 0),
  prefetchedState := Modules.Constant.certification (.vector 2 .bit) (stateOfNat 3),
  completedPhase := Modules.Mux.certification (.vector 2 .bit),
  valid := Modules.Mux.certification .bit,
  phase := Modules.Mux.certification (.vector 2 .bit),
  result := Modules.NamedTupleCombiner.certification stateMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    {.inputsFields, .currentFields, .updatedFields} =>
      Modules.NamedTupleSplitter.Rule.apply,
    .transfer => Primitives.AndRule.apply,
    .activeRead => Primitives.OrRule.apply,
    {.falseBit, .idleState, .prefetchedState} => Primitives.ConstantRule.apply,
    .completedPhase => Modules.Mux.Rule.select,
    {.valid, .phase} => Modules.Mux.Rule.select,
    .result => Modules.NamedTupleCombiner.Rule.apply]
  state := []

def structuralResult (memoryInputs : Inputs) (current updated : stateMap.Values) :
    stateMap.Values
  | .mem_state => bif memXfer memoryInputs current then
      bif memoryInputs.mem_do_rinst || memoryInputs.mem_do_rdata
        then stateOfNat 0 else stateOfNat 3
      else updated .mem_state
  | .mem_valid => bif memXfer memoryInputs current
      then false else updated .mem_valid
  | field => updated field

theorem structuralResult_eq_readNextState (memoryInputs : Inputs)
    (current updated : stateMap.Values) :
    structuralResult memoryInputs current updated =
      readNextState memoryInputs current updated := by
  cases valid : current .mem_valid <;> cases ready : memoryInputs.mem_ready <;>
    cases rinst : memoryInputs.mem_do_rinst <;>
    cases rdata : memoryInputs.mem_do_rdata <;>
    funext field <;> cases field <;>
    simp [structuralResult, readNextState, memXfer, memXferFrom, valid, ready,
      rinst, rdata, SignalMap.set]

section Certification

variable (layerChildren : ChildStructures body childContracts)

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.Implements (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro inputs contractState structuralStateValue proposal corresponds satisfies
  derive_empty_state_child_matches childMatch from
    layerChildren, inputs, structuralStateValue, proposal, satisfies

  let memoryInputs := Inputs.unpack (inputs .inputs)
  let current := stateMap.unpack (inputs .current)
  let updated := stateMap.unpack (inputs .updated)
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
  have updatedFieldsValue : (proposal.2 .updatedFields).outputs = updated := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .updatedFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [ProofSupport.splitValue_eq_unpack, updated] using equation
  have readyValue : (proposal.2 .inputsFields).outputs .mem_ready =
      memoryInputs.mem_ready := by rw [inputsFieldsValue]; rfl
  have rinstValue : (proposal.2 .inputsFields).outputs .mem_do_rinst =
      memoryInputs.mem_do_rinst := by rw [inputsFieldsValue]; rfl
  have rdataValue : (proposal.2 .inputsFields).outputs .mem_do_rdata =
      memoryInputs.mem_do_rdata := by rw [inputsFieldsValue]; rfl
  have transferValue : (proposal.2 .transfer).outputs .output =
      memXfer memoryInputs current := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .transfer).1.1 Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [currentFieldsValue, readyValue] at equation
    simpa [memXfer, memXferFrom] using equation
  have activeValue : (proposal.2 .activeRead).outputs .output =
      (memoryInputs.mem_do_rinst || memoryInputs.mem_do_rdata) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .activeRead).1.1 Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [rinstValue, rdataValue] at equation
    exact equation
  have falseValue := (Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    ((childMatch .falseBit).1.1 Primitives.ConstantRule.apply)
  have idleValue := (Modules.Constant.outputRule_holds_iff
    (.vector 2 .bit) (stateOfNat 0) _ _ _).mp
    ((childMatch .idleState).1.1 Primitives.ConstantRule.apply)
  have prefetchedValue := (Modules.Constant.outputRule_holds_iff
    (.vector 2 .bit) (stateOfNat 3) _ _ _).mp
    ((childMatch .prefetchedState).1.1 Primitives.ConstantRule.apply)
  have completedValue : (proposal.2 .completedPhase).outputs .result =
      bif memoryInputs.mem_do_rinst || memoryInputs.mem_do_rdata
        then stateOfNat 0 else stateOfNat 3 := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 2 .bit)
      _ _ _ _ (childMatch .completedPhase).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [activeValue, idleValue, prefetchedValue] at equation
    exact equation
  have validValue : (proposal.2 .valid).outputs .result =
      bif memXfer memoryInputs current then false else updated .mem_valid := by
    have equation := Modules.Mux.result_of_evaluatesTo .bit
      _ _ _ _ (childMatch .valid).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [transferValue, updatedFieldsValue, falseValue] at equation
    exact equation
  have phaseValue : (proposal.2 .phase).outputs .result =
      bif memXfer memoryInputs current then
        bif memoryInputs.mem_do_rinst || memoryInputs.mem_do_rdata
          then stateOfNat 0 else stateOfNat 3
        else updated .mem_state := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 2 .bit)
      _ _ _ _ (childMatch .phase).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [transferValue, updatedFieldsValue, completedValue] at equation
    exact equation

  have resultInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .result = structuralResult memoryInputs current updated := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, structuralResult]
    · exact phaseValue
    · exact validValue
    · simpa using congrFun updatedFieldsValue .mem_instr
    · simpa using congrFun updatedFieldsValue .mem_addr
    · simpa using congrFun updatedFieldsValue .mem_wdata
    · simpa using congrFun updatedFieldsValue .mem_wstrb
    · simpa using congrFun updatedFieldsValue .mem_rdata_q
  have resultValue : (proposal.2 .result).outputs .value =
      stateMap.pack (structuralResult memoryInputs current updated) := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .result).1.1 Modules.NamedTupleCombiner.Rule.apply)
    rw [resultInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [StateUpdate.outputRule_holds_iff]
    rw [show proposal.outputs .state = (proposal.2 .result).outputs .value by
      exact satisfies.1 .state]
    rw [resultValue, structuralResult_eq_readNextState]
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
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.Memory.ReadUpdate
