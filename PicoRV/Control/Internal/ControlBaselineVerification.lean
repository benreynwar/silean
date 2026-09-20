import PicoRV.Control.ControlBaseline
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems
import Silean.Primitives.And

namespace PicoRV.Control.Baseline

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  inputsFields := Silean.Modules.NamedTupleSplitter.certification ControlInputs.signalMap,
  currentFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  falseBit := Silean.Modules.Constant.certification .bit false,
  fetchCompleted := Silean.Primitives.andCertified.certification,
  result := Silean.Modules.NamedTupleCombiner.certification stateMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .apply => [
        {.inputsFields, .currentFields} => Silean.Modules.NamedTupleSplitter.Rule.apply,
        .falseBit => Silean.Primitives.ConstantRule.apply,
        .fetchCompleted => Silean.Primitives.AndRule.apply,
        .result => Silean.Modules.NamedTupleCombiner.Rule.apply]
  state := []

private theorem splitValue_eq_unpack (signals : Silean.SignalMap.{0})
    (value : signals.tupleType.Denote) :
    Silean.Modules.NamedTupleSplitter.splitValue signals value = signals.unpack value := by
  calc
    Silean.Modules.NamedTupleSplitter.splitValue signals value =
        Silean.Modules.NamedTupleSplitter.splitValue signals
          (signals.pack (signals.unpack value)) := by rw [signals.pack_unpack]
    _ = signals.unpack value :=
      Silean.Modules.NamedTupleSplitter.splitValue_pack signals _

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
  derive_empty_state_child_matches childMatch for body from
    layerChildren, hierStep, satisfies

  let controlInputs := Inputs.unpack (hierStep.inputs .inputs)
  let current := stateMap.unpack (hierStep.inputs .current)

  have inputsFieldsValue : hierStep.childOutputs .inputsFields =
      ControlInputs.signalMap.unpack (hierStep.inputs .inputs) := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      ControlInputs.signalMap _ _ _).mp
      ((childMatch .inputsFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    change hierStep.childOutputs .inputsFields =
      Silean.Modules.NamedTupleSplitter.splitValue ControlInputs.signalMap
        (hierStep.inputs .inputs) at equation
    exact equation.trans (splitValue_eq_unpack _ _)
  have currentFieldsValue : hierStep.childOutputs .currentFields = current := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .currentFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    change hierStep.childOutputs .currentFields =
      Silean.Modules.NamedTupleSplitter.splitValue stateMap
        (hierStep.inputs .current) at equation
    exact equation.trans ((splitValue_eq_unpack _ _).trans (by rfl))
  have memDoneValue : hierStep.childOutputs .inputsFields .mem_done =
      controlInputs.mem_done := by
    rw [inputsFieldsValue]
    rfl
  have falseValue := Silean.Modules.Constant.output_of_allowed .bit false
    (childMatch .falseBit).allowed
  have fetchCompletedValue : hierStep.childOutputs .fetchCompleted .output =
      ((current .mem_do_rinst : Bool) && controlInputs.mem_done) := by
    have equation := (Silean.Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .fetchCompleted).ruleHolds Silean.Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (apply₂_congr Bool.and
      (congrFun currentFieldsValue .mem_do_rinst) memDoneValue)

  have resultInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .result = baselineState controlInputs current := by
    funext field
    cases field <;> change hierStep.childOutputs _ _ = _ <;>
      simp only [baselineState, Silean.SignalMap.set]
    · simpa using congrFun currentFieldsValue .cpu_state
    · simpa using congrFun currentFieldsValue .latched_store
    · simpa using congrFun currentFieldsValue .latched_stalu
    · simpa using congrFun currentFieldsValue .latched_branch
    · simpa using congrFun currentFieldsValue .latched_is_lu
    · simpa using congrFun currentFieldsValue .latched_is_lh
    · simpa using congrFun currentFieldsValue .latched_is_lb
    · simpa using congrFun currentFieldsValue .latched_rd
    · simpa using congrFun currentFieldsValue .mem_wordsize
    · simpa using congrFun currentFieldsValue .mem_do_prefetch
    · simpa using congrFun currentFieldsValue .mem_do_rinst
    · simpa using congrFun currentFieldsValue .mem_do_rdata
    · simpa using congrFun currentFieldsValue .mem_do_wdata
    · exact fetchCompletedValue
    · exact falseValue
    · exact falseValue
  have resultValue : hierStep.childOutputs .result .value =
      stateMap.pack (baselineState controlInputs current) := by
    have equation := (Silean.Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .result).ruleHolds Silean.Modules.NamedTupleCombiner.Rule.apply)
    rw [resultInputs] at equation
    rw [equation, Silean.Modules.NamedTupleCombiner.combinedValue_eq_pack]

  refine ⟨Silean.SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [Baseline.outputRule_holds_iff]
    dsimp only
    rw [show hierStep.outputs .state = hierStep.childOutputs .result .value by
      exact satisfies.1 .state]
    simpa [Baseline.outputState, controlInputs, current] using resultValue
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

end PicoRV.Control.Baseline
