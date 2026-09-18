import PicoRV.Datapath.DatapathBasicUpdates
import PicoRV.Datapath.DatapathProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems

namespace PicoRV.Datapath.Baseline

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  currentFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  result := Silean.Modules.NamedTupleCombiner.certification stateMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output | .apply => [
    .currentFields => Silean.Modules.NamedTupleSplitter.Rule.apply,
    .result => Silean.Modules.NamedTupleCombiner.Rule.apply]
  state := []

section Certification

variable (layerChildren : ChildStructures body childContracts)

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (Silean.Contracts.Cycle.Certification.Layer.moduleStructure
      body layerChildren).State) : Prop := True

private theorem implements :
    Silean.Contracts.Cycle.ImplementsSolutions
      (Silean.Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  have childMatch (child : Instance) :=
    (childSolutionMatchesCoveredContract layerChildren hierStep
      satisfies child).choose_spec

  let current := stateMap.unpack (hierStep.inputs .current)
  have currentFieldsValue : hierStep.childOutputs .currentFields = current := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .currentFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    change hierStep.childOutputs .currentFields =
      Silean.Modules.NamedTupleSplitter.splitValue stateMap
        (hierStep.inputs .current) at equation
    exact equation.trans <| by rw [ProofSupport.splitValue_eq_unpack]

  have resultInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .result =
        baselineState (hierStep.inputs .alu_out) current := by
    funext field
    cases field
    · change hierStep.childOutputs .currentFields .reg_pc = _
      simpa [baselineState, Silean.SignalMap.set] using
        congrFun currentFieldsValue .reg_pc
    · change hierStep.childOutputs .currentFields .reg_next_pc = _
      simpa [baselineState, Silean.SignalMap.set] using
        congrFun currentFieldsValue .reg_next_pc
    · change hierStep.childOutputs .currentFields .reg_op1 = _
      simpa [baselineState, Silean.SignalMap.set] using
        congrFun currentFieldsValue .reg_op1
    · change hierStep.childOutputs .currentFields .reg_op2 = _
      simpa [baselineState, Silean.SignalMap.set] using
        congrFun currentFieldsValue .reg_op2
    · change hierStep.childOutputs .currentFields .reg_out = _
      simpa [baselineState, Silean.SignalMap.set] using
        congrFun currentFieldsValue .reg_out
    · change hierStep.childOutputs .currentFields .reg_sh = _
      simpa [baselineState, Silean.SignalMap.set] using
        congrFun currentFieldsValue .reg_sh
    · change hierStep.inputs .alu_out = _
      rfl
  have resultValue : hierStep.childOutputs .result .value =
      stateMap.pack (baselineState (hierStep.inputs .alu_out) current) := by
    have equation := (Silean.Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .result).ruleHolds Silean.Modules.NamedTupleCombiner.Rule.apply)
    rw [resultInputs] at equation
    rw [equation, Silean.Modules.NamedTupleCombiner.combinedValue_eq_pack]

  refine ⟨Silean.SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    dsimp only
    rw [show hierStep.outputs .state = hierStep.childOutputs .result .value by
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
  stateCoverage := fun _ _ => ⟨Silean.SignalMap.emptyValues, trivial⟩,
  implements := implements

end PicoRV.Datapath.Baseline
