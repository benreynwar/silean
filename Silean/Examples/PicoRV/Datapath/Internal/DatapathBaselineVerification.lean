import Silean.Examples.PicoRV.Datapath.DatapathBasicUpdates
import Silean.Examples.PicoRV.Datapath.DatapathProofSupport
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems

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

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (Contracts.Cycle.Certification.Layer.moduleStructure
      body layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  have childMatch (child : Instance) :=
    (childSolutionMatchesCoveredContract layerChildren hierStep
      satisfies child).choose_spec

  let current := stateMap.unpack (hierStep.inputs .current)
  have currentFieldsValue : hierStep.childOutputs .currentFields = current := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .currentFields).ruleHolds Modules.NamedTupleSplitter.Rule.apply)
    change hierStep.childOutputs .currentFields =
      Modules.NamedTupleSplitter.splitValue stateMap
        (hierStep.inputs .current) at equation
    exact equation.trans <| by rw [ProofSupport.splitValue_eq_unpack]

  have resultInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .result =
        baselineState (hierStep.inputs .alu_out) current := by
    funext field
    cases field
    · change hierStep.childOutputs .currentFields .reg_pc = _
      simpa [baselineState, SignalMap.set] using
        congrFun currentFieldsValue .reg_pc
    · change hierStep.childOutputs .currentFields .reg_next_pc = _
      simpa [baselineState, SignalMap.set] using
        congrFun currentFieldsValue .reg_next_pc
    · change hierStep.childOutputs .currentFields .reg_op1 = _
      simpa [baselineState, SignalMap.set] using
        congrFun currentFieldsValue .reg_op1
    · change hierStep.childOutputs .currentFields .reg_op2 = _
      simpa [baselineState, SignalMap.set] using
        congrFun currentFieldsValue .reg_op2
    · change hierStep.childOutputs .currentFields .reg_out = _
      simpa [baselineState, SignalMap.set] using
        congrFun currentFieldsValue .reg_out
    · change hierStep.childOutputs .currentFields .reg_sh = _
      simpa [baselineState, SignalMap.set] using
        congrFun currentFieldsValue .reg_sh
    · change hierStep.inputs .alu_out = _
      rfl
  have resultValue : hierStep.childOutputs .result .value =
      stateMap.pack (baselineState (hierStep.inputs .alu_out) current) := by
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

end Silean.Examples.PicoRV.Datapath.Baseline
