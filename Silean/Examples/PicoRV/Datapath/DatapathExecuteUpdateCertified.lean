import Silean.Examples.PicoRV.Datapath.DatapathBasicUpdates
import Silean.Examples.PicoRV.Datapath.DatapathProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Add.Add
import Silean.Modules.Constant.Constant
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified

namespace Silean.Examples.PicoRV.Datapath.ExecuteUpdate

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

set_option maxRecDepth 4096

module_child_certifications childContracts for body where
  inputsFields := Modules.NamedTupleSplitter.certification DatapathInputs.signalMap,
  currentFields := Modules.NamedTupleSplitter.certification stateMap,
  updatedFields := Modules.NamedTupleSplitter.certification stateMap,
  falseBit := Modules.Constant.certification .bit false,
  target := Modules.Add.certification 32,
  result := Modules.NamedTupleCombiner.certification stateMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    {.inputsFields, .currentFields, .updatedFields} =>
      Modules.NamedTupleSplitter.Rule.apply,
    .falseBit => Primitives.ConstantRule.apply,
    .target => Modules.Add.Rule.apply,
    .result => Modules.NamedTupleCombiner.Rule.apply]
  state := []

section Certification

variable (layerChildren : ChildStructures body childContracts)

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.Implements (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  derive_empty_state_child_matches childMatch from
    layerChildren, inputs, structuralState, proposal, satisfies

  let datapathInputs := Inputs.unpack (inputs .inputs)
  let current := stateMap.unpack (inputs .current)
  let updated := stateMap.unpack (inputs .updated)
  have inputsFieldsValue : (proposal.2 .inputsFields).outputs =
      DatapathInputs.signalMap.unpack (inputs .inputs) := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      DatapathInputs.signalMap _ _ _).mp
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
  have decodedImmValue : (proposal.2 .inputsFields).outputs .decoded_imm =
      datapathInputs.decoded_imm := by rw [inputsFieldsValue]; rfl
  have falseValue := (Modules.Constant.outputRule_holds_iff .bit false _ _ _).mp
    ((childMatch .falseBit).1.1 Primitives.ConstantRule.apply)
  have targetValue : (proposal.2 .target).outputs .result =
      addWords (current .reg_pc) datapathInputs.decoded_imm := by
    have equation := Modules.Add.result_of_evaluatesTo 32
      _ _ _ _ (childMatch .target).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [currentFieldsValue, decodedImmValue, falseValue,
      ProofSupport.addBits_eq_addWords] at equation
    exact equation

  have resultInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .result = executeNextState datapathInputs current updated := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value,
        executeNextState, SignalMap.set]
    · simpa using congrFun updatedFieldsValue .reg_pc
    · simpa using congrFun updatedFieldsValue .reg_next_pc
    · simpa using congrFun updatedFieldsValue .reg_op1
    · simpa using congrFun updatedFieldsValue .reg_op2
    · exact targetValue
    · simpa using congrFun updatedFieldsValue .reg_sh
    · simpa using congrFun updatedFieldsValue .alu_out_q
  have resultValue : (proposal.2 .result).outputs .value =
      stateMap.pack (executeNextState datapathInputs current updated) := by
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
    simpa [StateUpdate.outputState, datapathInputs, current, updated] using resultValue
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

end Silean.Examples.PicoRV.Datapath.ExecuteUpdate
