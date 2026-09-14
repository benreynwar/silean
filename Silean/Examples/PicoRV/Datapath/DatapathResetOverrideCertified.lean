import Silean.Examples.PicoRV.Datapath.DatapathBasicUpdates
import Silean.Examples.PicoRV.Datapath.DatapathProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.MuxCertified
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified

namespace Silean.Examples.PicoRV.Datapath.ResetOverride

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  selectedFields := Modules.NamedTupleSplitter.certification stateMap,
  zeroWord := Modules.Constant.certification (.vector 32 .bit) (wordOfNat 0),
  pc := Modules.Mux.certification (.vector 32 .bit),
  nextPc := Modules.Mux.certification (.vector 32 .bit),
  result := Modules.NamedTupleCombiner.certification stateMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    .selectedFields => Modules.NamedTupleSplitter.Rule.apply,
    .zeroWord => Primitives.ConstantRule.apply,
    {.pc, .nextPc} => Modules.Mux.Rule.select,
    .result => Modules.NamedTupleCombiner.Rule.apply]
  state := []

def structuralState (resetn : Bool) (selected : stateMap.Values) : stateMap.Values
  | .reg_pc => bif resetn then selected .reg_pc else wordOfNat 0
  | .reg_next_pc => bif resetn then selected .reg_next_pc else wordOfNat 0
  | field => selected field

theorem structuralState_eq_resetApplied (resetn : Bool)
    (selected : stateMap.Values) :
    structuralState resetn selected = resetApplied resetn selected := by
  cases resetn <;> funext field <;> cases field <;>
    simp [structuralState, resetApplied, SignalMap.set]

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

  let selected := stateMap.unpack (inputs .selected)
  have selectedFieldsValue : (proposal.2 .selectedFields).outputs = selected := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .selectedFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [ProofSupport.splitValue_eq_unpack, selected] using equation
  have zeroValue := (Modules.Constant.outputRule_holds_iff
    (.vector 32 .bit) (wordOfNat 0) _ _ _).mp
    ((childMatch .zeroWord).1.1 Primitives.ConstantRule.apply)
  have pcValue : (proposal.2 .pc).outputs .result =
      bif inputs .resetn then selected .reg_pc else wordOfNat 0 := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .pc).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [selectedFieldsValue, zeroValue] at equation
    exact equation
  have nextPcValue : (proposal.2 .nextPc).outputs .result =
      bif inputs .resetn then selected .reg_next_pc else wordOfNat 0 := by
    have equation := Modules.Mux.result_of_evaluatesTo (.vector 32 .bit)
      _ _ _ _ (childMatch .nextPc).1
    normalize_child_hyp equation unfolding body, wiring, context
    rw [selectedFieldsValue, zeroValue] at equation
    exact equation

  have resultInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .result = structuralState (inputs .resetn) selected := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, structuralState]
    · exact pcValue
    · exact nextPcValue
    · simpa using congrFun selectedFieldsValue .reg_op1
    · simpa using congrFun selectedFieldsValue .reg_op2
    · simpa using congrFun selectedFieldsValue .reg_out
    · simpa using congrFun selectedFieldsValue .reg_sh
    · simpa using congrFun selectedFieldsValue .alu_out_q
  have resultValue : (proposal.2 .result).outputs .value =
      stateMap.pack (structuralState (inputs .resetn) selected) := by
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
    rw [resultValue, structuralState_eq_resetApplied]
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

end Silean.Examples.PicoRV.Datapath.ResetOverride
