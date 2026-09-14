import Silean.Examples.PicoRV.Control.ControlCommandFinish
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified
import Silean.Primitives.And
import Silean.Primitives.Not
import Silean.Primitives.Or

namespace Silean.Examples.PicoRV.Control.CommandFinish

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  transitionFields := Modules.NamedTupleSplitter.certification
    TransitionValue.signalMap,
  stateFields := Modules.NamedTupleSplitter.certification stateMap,
  notClear := Primitives.notCertified.certification,
  keepPrefetch := Primitives.andCertified.certification,
  keepRinst := Primitives.andCertified.certification,
  keepRdata := Primitives.andCertified.certification,
  keepWdata := Primitives.andCertified.certification,
  finishRinst := Primitives.orCertified.certification,
  finishRdata := Primitives.orCertified.certification,
  finishWdata := Primitives.orCertified.certification,
  result := Modules.NamedTupleCombiner.certification stateMap

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .apply => [
        .transitionFields => Modules.NamedTupleSplitter.Rule.apply,
        .stateFields => Modules.NamedTupleSplitter.Rule.apply,
        .notClear => Primitives.NotRule.apply,
        {.keepPrefetch, .keepRinst, .keepRdata, .keepWdata} =>
          Primitives.AndRule.apply,
        {.finishRinst, .finishRdata, .finishWdata} => Primitives.OrRule.apply,
        .result => Modules.NamedTupleCombiner.Rule.apply]
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
    simp [structuralResult, finishCommands, commandsCleared, SignalMap.set]

private theorem splitValue_eq_unpack (signals : SignalMap.{0})
    (value : signals.tupleType.Denote) :
    Modules.NamedTupleSplitter.splitValue signals value = signals.unpack value := by
  calc
    Modules.NamedTupleSplitter.splitValue signals value =
        Modules.NamedTupleSplitter.splitValue signals
          (signals.pack (signals.unpack value)) := by
      rw [signals.pack_unpack]
    _ = signals.unpack value :=
      Modules.NamedTupleSplitter.splitValue_pack signals _

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

  have transitionFieldsValue :
      (proposal.2 .transitionFields).outputs =
        TransitionValue.signalMap.unpack (inputs .transition) := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      TransitionValue.signalMap _ _ _).mp
      ((childMatch .transitionFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [splitValue_eq_unpack] using equation

  let transition := Transition.unpack (inputs .transition)

  have stateFieldsValue :
      (proposal.2 .stateFields).outputs = transition.state := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .stateFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [transitionFieldsValue] at equation
    rw [splitValue_eq_unpack] at equation
    exact equation

  have notClearValue : (proposal.2 .notClear).outputs .output = !inputs .clear := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notClear).1.1 Primitives.NotRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    exact equation

  have keepPrefetchValue : (proposal.2 .keepPrefetch).outputs .output =
      (transition.state .mem_do_prefetch && !inputs .clear) := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .keepPrefetch).1.1 Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [stateFieldsValue, notClearValue] at equation
    exact equation

  have keepRinstValue : (proposal.2 .keepRinst).outputs .output =
      (transition.state .mem_do_rinst && !inputs .clear) := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .keepRinst).1.1 Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [stateFieldsValue, notClearValue] at equation
    exact equation

  have keepRdataValue : (proposal.2 .keepRdata).outputs .output =
      (transition.state .mem_do_rdata && !inputs .clear) := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .keepRdata).1.1 Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [stateFieldsValue, notClearValue] at equation
    exact equation

  have keepWdataValue : (proposal.2 .keepWdata).outputs .output =
      (transition.state .mem_do_wdata && !inputs .clear) := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .keepWdata).1.1 Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [stateFieldsValue, notClearValue] at equation
    exact equation

  have finishRinstValue : (proposal.2 .finishRinst).outputs .output =
      ((transition.state .mem_do_rinst && !inputs .clear) || transition.setRinst) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .finishRinst).1.1 Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [keepRinstValue, transitionFieldsValue] at equation
    exact equation

  have finishRdataValue : (proposal.2 .finishRdata).outputs .output =
      ((transition.state .mem_do_rdata && !inputs .clear) || transition.setRdata) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .finishRdata).1.1 Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [keepRdataValue, transitionFieldsValue] at equation
    exact equation

  have finishWdataValue : (proposal.2 .finishWdata).outputs .output =
      ((transition.state .mem_do_wdata && !inputs .clear) || transition.setWdata) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .finishWdata).1.1 Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [keepWdataValue, transitionFieldsValue] at equation
    exact equation

  have resultInputsEqual : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .result = structuralResult (inputs .clear) transition := by
    funext field
    cases field <;>
      simp only [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, structuralResult]
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

  have resultValue : (proposal.2 .result).outputs .value =
      stateMap.pack (structuralResult (inputs .clear) transition) := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .result).1.1 Modules.NamedTupleCombiner.Rule.apply)
    rw [resultInputsEqual] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]

  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    rw [show proposal.outputs .state = (proposal.2 .result).outputs .value by
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
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

/-- The command-finishing module and all of its aggregate adapters and Boolean
children are concrete. -/
theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.Control.CommandFinish
