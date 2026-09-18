import PicoRV.Control.ControlCommandFinish
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems
import Silean.Primitives.And
import Silean.Primitives.Not
import Silean.Primitives.Or

namespace PicoRV.Control.CommandFinish

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  transitionFields := Silean.Modules.NamedTupleSplitter.certification
    TransitionValue.signalMap,
  stateFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  notClear := Silean.Primitives.notCertified.certification,
  keepPrefetch := Silean.Primitives.andCertified.certification,
  keepRinst := Silean.Primitives.andCertified.certification,
  keepRdata := Silean.Primitives.andCertified.certification,
  keepWdata := Silean.Primitives.andCertified.certification,
  finishRinst := Silean.Primitives.orCertified.certification,
  finishRdata := Silean.Primitives.orCertified.certification,
  finishWdata := Silean.Primitives.orCertified.certification,
  result := Silean.Modules.NamedTupleCombiner.certification stateMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .apply => [
        .transitionFields => Silean.Modules.NamedTupleSplitter.Rule.apply,
        .stateFields => Silean.Modules.NamedTupleSplitter.Rule.apply,
        .notClear => Silean.Primitives.NotRule.apply,
        {.keepPrefetch, .keepRinst, .keepRdata, .keepWdata} =>
          Silean.Primitives.AndRule.apply,
        {.finishRinst, .finishRdata, .finishWdata} => Silean.Primitives.OrRule.apply,
        .result => Silean.Modules.NamedTupleCombiner.Rule.apply]
  state := []

def structuralResult (clear : Bool) (transition : Transition) : stateMap.Values :=
  fun
  | .mem_do_prefetch => transition.state .mem_do_prefetch && !clear
  | .mem_do_rinst =>
      (transition.state .mem_do_rinst && !clear) || transition.setRinst
  | .mem_do_rdata =>
      (transition.state .mem_do_rdata && !clear) || transition.setRdata
  | .mem_do_wdata =>
      (transition.state .mem_do_wdata && !clear) || transition.setWdata
  | field => transition.state field

theorem structuralResult_eq_finishCommands (clear : Bool) (transition : Transition) :
    structuralResult clear transition = finishCommands clear transition := by
  rcases transition with ⟨state, setRinst, setRdata, setWdata⟩
  cases clear <;> cases setRinst <;> cases setRdata <;> cases setWdata <;>
    funext field <;> cases field <;>
    simp [structuralResult, finishCommands, commandsCleared, Silean.SignalMap.set]

private theorem splitValue_eq_unpack (signals : Silean.SignalMap.{0})
    (value : signals.tupleType.Denote) :
    Silean.Modules.NamedTupleSplitter.splitValue signals value = signals.unpack value := by
  calc
    Silean.Modules.NamedTupleSplitter.splitValue signals value =
        Silean.Modules.NamedTupleSplitter.splitValue signals
          (signals.pack (signals.unpack value)) := by
      rw [signals.pack_unpack]
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

  have transitionFieldsValue :
      hierStep.childOutputs .transitionFields =
        TransitionValue.signalMap.unpack (hierStep.inputs .transition) := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      TransitionValue.signalMap _ _ _).mp
      ((childMatch .transitionFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    change hierStep.childOutputs .transitionFields =
      Silean.Modules.NamedTupleSplitter.splitValue TransitionValue.signalMap
        (hierStep.inputs .transition) at equation
    exact equation.trans (splitValue_eq_unpack _ _)

  let transition := Transition.unpack (hierStep.inputs .transition)

  have stateFieldsValue :
      hierStep.childOutputs .stateFields = transition.state := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .stateFields).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans <| (congrArg
      (Silean.Modules.NamedTupleSplitter.splitValue stateMap)
      (congrFun transitionFieldsValue .state)).trans
        ((splitValue_eq_unpack _ _).trans (by rfl))

  have notClearValue : hierStep.childOutputs .notClear .output =
      !hierStep.inputs .clear := by
    have equation := (Silean.Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notClear).ruleHolds Silean.Primitives.NotRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation

  have keepPrefetchValue : hierStep.childOutputs .keepPrefetch .output =
      (transition.state .mem_do_prefetch && !hierStep.inputs .clear) := by
    have equation := (Silean.Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .keepPrefetch).ruleHolds Silean.Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (apply₂_congr Bool.and
      (congrFun stateFieldsValue .mem_do_prefetch) notClearValue)

  have keepRinstValue : hierStep.childOutputs .keepRinst .output =
      (transition.state .mem_do_rinst && !hierStep.inputs .clear) := by
    have equation := (Silean.Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .keepRinst).ruleHolds Silean.Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (apply₂_congr Bool.and
      (congrFun stateFieldsValue .mem_do_rinst) notClearValue)

  have keepRdataValue : hierStep.childOutputs .keepRdata .output =
      (transition.state .mem_do_rdata && !hierStep.inputs .clear) := by
    have equation := (Silean.Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .keepRdata).ruleHolds Silean.Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (apply₂_congr Bool.and
      (congrFun stateFieldsValue .mem_do_rdata) notClearValue)

  have keepWdataValue : hierStep.childOutputs .keepWdata .output =
      (transition.state .mem_do_wdata && !hierStep.inputs .clear) := by
    have equation := (Silean.Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .keepWdata).ruleHolds Silean.Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (apply₂_congr Bool.and
      (congrFun stateFieldsValue .mem_do_wdata) notClearValue)

  have finishRinstValue : hierStep.childOutputs .finishRinst .output =
      ((transition.state .mem_do_rinst && !hierStep.inputs .clear) ||
        transition.setRinst) := by
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .finishRinst).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (apply₂_congr Bool.or keepRinstValue
      (congrFun transitionFieldsValue .setRinst))

  have finishRdataValue : hierStep.childOutputs .finishRdata .output =
      ((transition.state .mem_do_rdata && !hierStep.inputs .clear) ||
        transition.setRdata) := by
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .finishRdata).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (apply₂_congr Bool.or keepRdataValue
      (congrFun transitionFieldsValue .setRdata))

  have finishWdataValue : hierStep.childOutputs .finishWdata .output =
      ((transition.state .mem_do_wdata && !hierStep.inputs .clear) ||
        transition.setWdata) := by
    have equation := (Silean.Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .finishWdata).ruleHolds Silean.Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (apply₂_congr Bool.or keepWdataValue
      (congrFun transitionFieldsValue .setWdata))

  have resultInputsEqual : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .result =
        structuralResult (hierStep.inputs .clear) transition := by
    funext field
    cases field <;> change hierStep.childOutputs _ _ = _ <;>
      simp only [structuralResult]
    all_goals first
      | simpa using congrFun stateFieldsValue ControlState.Field.cpu_state
      | simpa using congrFun stateFieldsValue ControlState.Field.latched_store
      | simpa using congrFun stateFieldsValue ControlState.Field.latched_stalu
      | simpa using congrFun stateFieldsValue ControlState.Field.latched_branch
      | simpa using congrFun stateFieldsValue ControlState.Field.latched_is_lu
      | simpa using congrFun stateFieldsValue ControlState.Field.latched_is_lh
      | simpa using congrFun stateFieldsValue ControlState.Field.latched_is_lb
      | simpa using congrFun stateFieldsValue ControlState.Field.latched_rd
      | simpa using congrFun stateFieldsValue ControlState.Field.mem_wordsize
      | exact keepPrefetchValue
      | exact finishRinstValue
      | exact finishRdataValue
      | exact finishWdataValue
      | simpa using congrFun stateFieldsValue ControlState.Field.decoder_trigger
      | simpa using congrFun stateFieldsValue ControlState.Field.decoder_pseudo_trigger
      | simpa using congrFun stateFieldsValue ControlState.Field.trap

  have resultValue : hierStep.childOutputs .result .value =
      stateMap.pack (structuralResult (hierStep.inputs .clear) transition) := by
    have equation := (Silean.Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .result).ruleHolds Silean.Modules.NamedTupleCombiner.Rule.apply)
    rw [resultInputsEqual] at equation
    rw [equation, Silean.Modules.NamedTupleCombiner.combinedValue_eq_pack]

  have boundary := satisfies.1
  refine ⟨Silean.SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    dsimp only
    rw [show hierStep.outputs .state = hierStep.childOutputs .result .value by
      exact boundary .state]
    rw [resultValue, structuralResult_eq_finishCommands]
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

end PicoRV.Control.CommandFinish
