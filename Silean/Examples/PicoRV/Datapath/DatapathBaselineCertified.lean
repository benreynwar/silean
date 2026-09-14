import Silean.Examples.PicoRV.Datapath.DatapathBasicUpdates
import Silean.Examples.PicoRV.Datapath.DatapathProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified

namespace Silean.Examples.PicoRV.Datapath.Baseline

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  currentFields := Modules.NamedTupleSplitter.certification stateMap,
  result := Modules.NamedTupleCombiner.certification stateMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    .currentFields => Modules.NamedTupleSplitter.Rule.apply,
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

  let current := stateMap.unpack (inputs .current)
  have currentFieldsValue : (proposal.2 .currentFields).outputs = current := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .currentFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [ProofSupport.splitValue_eq_unpack, current] using equation

  have resultInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .result = baselineState (inputs .alu_out) current := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, EndpointContext.moduleInput,
        SignalSource.value, baselineState, SignalMap.set]
    · simpa using congrFun currentFieldsValue .reg_pc
    · simpa using congrFun currentFieldsValue .reg_next_pc
    · simpa using congrFun currentFieldsValue .reg_op1
    · simpa using congrFun currentFieldsValue .reg_op2
    · simpa using congrFun currentFieldsValue .reg_out
    · simpa using congrFun currentFieldsValue .reg_sh
    · rfl
  have resultValue : (proposal.2 .result).outputs .value =
      stateMap.pack (baselineState (inputs .alu_out) current) := by
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
    simpa [outputState, current] using resultValue
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

end Silean.Examples.PicoRV.Datapath.Baseline
