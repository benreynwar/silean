import Silean.Examples.PicoRV.ControlStructure
import Silean.Examples.PicoRV.Control.ControlBitLaws
import Silean.Examples.PicoRV.Control.Internal.ControlNextVerification
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.EqualsConstant.EqualsConstantTheorems
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems
import Silean.Modules.Register.RegisterTheorems
import Silean.Primitives.And
import Silean.Primitives.Or

namespace Silean.Examples.PicoRV.Control

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  inputsValue := Modules.NamedTupleCombiner.certification
    ControlInputs.signalMap,
  storage := Modules.Register.certification stateType,
  stateFields := Modules.NamedTupleSplitter.certification stateMap,
  next := ControlNext.certification,
  fetchPhase := Modules.EqualsConstant.certification (.vector 8 .bit)
    (stateBits cpuStateFetch),
  writePending := Primitives.orCertified.certification,
  cpuregsWrite := Primitives.andCertified.certification

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .outputs => [
        .storage => Primitives.RegisterRule.observe,
        .stateFields => Modules.NamedTupleSplitter.Rule.apply,
        .fetchPhase => Modules.EqualsConstant.Rule.apply,
        .writePending => Primitives.OrRule.apply,
        .cpuregsWrite => Primitives.AndRule.apply]
  state := [
    .inputsValue => Modules.NamedTupleCombiner.Rule.apply,
    .storage => Primitives.RegisterRule.observe,
    .next => ControlNext.Rule.apply]

private theorem splitValue_eq_unpack (signals : SignalMap.{0})
    (value : signals.tupleType.Denote) :
    Modules.NamedTupleSplitter.splitValue signals value = signals.unpack value := by
  calc
    Modules.NamedTupleSplitter.splitValue signals value =
        Modules.NamedTupleSplitter.splitValue signals
          (signals.pack (signals.unpack value)) := by rw [signals.pack_unpack]
    _ = signals.unpack value :=
      Modules.NamedTupleSplitter.splitValue_pack signals _

private theorem equalFetchState (bits : Fin 8 → Bool) :
    (SignalType.vector 8 .bit).equal bits (stateBits cpuStateFetch) =
      decide (BitVector.toNat 8 bits = cpuStateFetch) := by
  have representation : stateBits cpuStateFetch =
      BitVector.ofNat 8 cpuStateFetch := by
    funext index
    simp [stateBits, BitVector.ofNat]
  rw [representation]
  exact signalTypeEqual_ofNat 8 cpuStateFetch bits (by decide)

section LayerCertification

variable (layerChildren : ChildStructures body childContracts)

/-! The sole structural state is the aggregate register. It corresponds to
the contract state exactly when the register's stored tuple is the packing of
those sixteen named fields. -/
private def stateCorresponds (contractState : cycleContract.state.Values)
    (structuralState : (Contracts.Cycle.Certification.Layer.moduleStructure
      body layerChildren).State) : Prop :=
  (layerChildren .storage).certification.stateCorresponds
    (fun | .stored => stateMap.pack contractState)
    (structuralState .storage)

private theorem hasCorrespondingState
    (structuralState : (Contracts.Cycle.Certification.Layer.moduleStructure
      body layerChildren).State) :
    ∃ contractState, stateCorresponds layerChildren contractState structuralState := by
  rcases (layerChildren .storage).certification.hasCorrespondingState
      (structuralState .storage) with ⟨storageState, storageCorresponds⟩
  refine ⟨stateMap.unpack (storageState .stored), ?_⟩
  change (layerChildren .storage).certification.stateCorresponds
    (fun | .stored => stateMap.pack (stateMap.unpack (storageState .stored)))
    (structuralState .storage)
  simpa using storageCorresponds

private theorem implements :
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies

  have coveredMatch (child : Instance) :=
    (childSolutionMatchesCoveredContract layerChildren hierStep satisfies child).choose_spec
  have inputsValueMatch := coveredMatch .inputsValue
  have stateFieldsMatch := coveredMatch .stateFields
  have nextMatch := coveredMatch .next
  have fetchPhaseMatch := coveredMatch .fetchPhase
  have writePendingMatch := coveredMatch .writePending
  have cpuregsWriteMatch := coveredMatch .cpuregsWrite
  have storageMatch := childSolutionMatchesContract layerChildren hierStep
    satisfies .storage
    (fun | .stored => stateMap.pack contractState) corresponds

  have inputsValueInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .inputsValue =
        (inputsOfValues hierStep.inputs).toValues := by
    funext field
    cases field <;>
      simp [body, wiring, context,
        EndpointContext.moduleInput, SignalSource.value, Inputs.toValues,
        inputsOfValues]
  have inputsValueValue : hierStep.childOutputs .inputsValue .value =
      (inputsOfValues hierStep.inputs).pack := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      ControlInputs.signalMap _ _ _).mp
      (inputsValueMatch.ruleHolds Modules.NamedTupleCombiner.Rule.apply)
    rw [inputsValueInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]
    rfl

  have storageOutputValue : hierStep.childOutputs .storage .output =
      stateMap.pack contractState := by
    have equation := (Modules.Register.outputRule_holds_iff stateType _ _ _).mp
      (storageMatch.ruleHolds Primitives.RegisterRule.observe)
    exact equation
  have stateFieldsValue : hierStep.childOutputs .stateFields = contractState := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      (stateFieldsMatch.ruleHolds Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans <| ((congrArg
      (Modules.NamedTupleSplitter.splitValue stateMap)
      storageOutputValue).trans <| by
        rw [splitValue_eq_unpack, stateMap.unpack_pack])

  have nextValue : hierStep.childOutputs .next .state =
      stateMap.pack (nextState (inputsOfValues hierStep.inputs) contractState) := by
    have equation := (ControlNext.outputRule_holds_iff _ _ _).mp
      (nextMatch.ruleHolds ControlNext.Rule.apply)
    have nextInputs : body.wiring.childInputValues hierStep.inputs
        hierStep.childOutputs .next =
          (fun
            | .inputs => (inputsOfValues hierStep.inputs).pack
            | .current => stateMap.pack contractState) := by
      funext input
      cases input <;>
        change hierStep.childOutputs _ _ = _
      · exact inputsValueValue
      · exact storageOutputValue
    rw [nextInputs] at equation
    simpa [ControlNext.outputState] using equation

  have fetchPhaseValue : hierStep.childOutputs .fetchPhase .result =
      decide (phase contractState = cpuStateFetch) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 8 .bit) (stateBits cpuStateFetch) _ _ _).mp
      (fetchPhaseMatch.ruleHolds Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans <| ((congrArg
      (fun value => (SignalType.vector 8 .bit).equal value
        (stateBits cpuStateFetch))
      (congrFun stateFieldsValue .cpu_state)).trans <| by
        rw [equalFetchState]
        rfl)
  have writePendingValue : hierStep.childOutputs .writePending .output =
      ((contractState .latched_branch : Bool) || contractState .latched_store) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      (writePendingMatch.ruleHolds Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans <| apply₂_congr Bool.or
      (congrFun stateFieldsValue .latched_branch)
      (congrFun stateFieldsValue .latched_store)
  have cpuregsWriteValue : hierStep.childOutputs .cpuregsWrite .output =
      cpuregsWrite contractState := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      (cpuregsWriteMatch.ruleHolds Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans <| (apply₂_congr Bool.and
      fetchPhaseValue writePendingValue).trans <| by
        simp only [cpuregsWrite]

  let nextContractState := stateRule.apply hierStep.inputs contractState
  refine ⟨nextContractState, ?_, ?_⟩
  · constructor
    · intro rule
      dsimp only
      cases rule
      rw [outputRule_holds_iff]
      funext output
      cases output
      · rw [show hierStep.outputs .cpuregs_write =
            hierStep.childOutputs .cpuregsWrite .output by
            exact satisfies.1 .cpuregs_write]
        exact cpuregsWriteValue
      · rw [show hierStep.outputs .cpu_state =
            hierStep.childOutputs .stateFields .cpu_state by
            exact satisfies.1 .cpu_state]
        exact congrFun stateFieldsValue .cpu_state
      · rw [show hierStep.outputs .latched_store =
            hierStep.childOutputs .stateFields .latched_store by
            exact satisfies.1 .latched_store]
        exact congrFun stateFieldsValue .latched_store
      · rw [show hierStep.outputs .latched_stalu =
            hierStep.childOutputs .stateFields .latched_stalu by
            exact satisfies.1 .latched_stalu]
        exact congrFun stateFieldsValue .latched_stalu
      · rw [show hierStep.outputs .latched_branch =
            hierStep.childOutputs .stateFields .latched_branch by
            exact satisfies.1 .latched_branch]
        exact congrFun stateFieldsValue .latched_branch
      · rw [show hierStep.outputs .latched_is_lu =
            hierStep.childOutputs .stateFields .latched_is_lu by
            exact satisfies.1 .latched_is_lu]
        exact congrFun stateFieldsValue .latched_is_lu
      · rw [show hierStep.outputs .latched_is_lh =
            hierStep.childOutputs .stateFields .latched_is_lh by
            exact satisfies.1 .latched_is_lh]
        exact congrFun stateFieldsValue .latched_is_lh
      · rw [show hierStep.outputs .latched_is_lb =
            hierStep.childOutputs .stateFields .latched_is_lb by
            exact satisfies.1 .latched_is_lb]
        exact congrFun stateFieldsValue .latched_is_lb
      · rw [show hierStep.outputs .latched_rd =
            hierStep.childOutputs .stateFields .latched_rd by
            exact satisfies.1 .latched_rd]
        exact congrFun stateFieldsValue .latched_rd
      · rw [show hierStep.outputs .mem_wordsize =
            hierStep.childOutputs .stateFields .mem_wordsize by
            exact satisfies.1 .mem_wordsize]
        exact congrFun stateFieldsValue .mem_wordsize
      · rw [show hierStep.outputs .mem_do_prefetch =
            hierStep.childOutputs .stateFields .mem_do_prefetch by
            exact satisfies.1 .mem_do_prefetch]
        exact congrFun stateFieldsValue .mem_do_prefetch
      · rw [show hierStep.outputs .mem_do_rinst =
            hierStep.childOutputs .stateFields .mem_do_rinst by
            exact satisfies.1 .mem_do_rinst]
        exact congrFun stateFieldsValue .mem_do_rinst
      · rw [show hierStep.outputs .mem_do_rdata =
            hierStep.childOutputs .stateFields .mem_do_rdata by
            exact satisfies.1 .mem_do_rdata]
        exact congrFun stateFieldsValue .mem_do_rdata
      · rw [show hierStep.outputs .mem_do_wdata =
            hierStep.childOutputs .stateFields .mem_do_wdata by
            exact satisfies.1 .mem_do_wdata]
        exact congrFun stateFieldsValue .mem_do_wdata
      · rw [show hierStep.outputs .decoder_trigger =
            hierStep.childOutputs .stateFields .decoder_trigger by
            exact satisfies.1 .decoder_trigger]
        exact congrFun stateFieldsValue .decoder_trigger
      · rw [show hierStep.outputs .decoder_pseudo_trigger =
            hierStep.childOutputs .stateFields .decoder_pseudo_trigger by
            exact satisfies.1 .decoder_pseudo_trigger]
        exact congrFun stateFieldsValue .decoder_pseudo_trigger
      · rw [show hierStep.outputs .trap =
            hierStep.childOutputs .stateFields .trap by
            exact satisfies.1 .trap]
        exact congrFun stateFieldsValue .trap
    · rfl
  · change (layerChildren .storage).certification.stateCorresponds
      (fun | .stored => stateMap.pack nextContractState)
      (HierStep.nextState (layerChildren .storage).moduleStructure
        (hierStep.children .storage))
    rw [show (fun _ => stateMap.pack nextContractState) =
        (childContracts .storage).stateRule.apply
          (body.wiring.childInputValues hierStep.inputs
            hierStep.childOutputs .storage)
          (fun _ => stateMap.pack contractState) by
      funext storageState
      cases storageState
      change stateMap.pack (nextState (inputsOfValues hierStep.inputs) contractState) =
        hierStep.childOutputs .next .state
      exact nextValue.symm]
    exact storageMatch.nextCorresponds

end LayerCertification

module_cycle_certification certification for moduleStructure via body
    with childContracts implementing cycleContract where
  schedules := derivedRuleSchedules,
  structuralChildren := structuralChildren,
  certifiedChildren := certifiedChildren,
  structuresMatch := certifiedChildren_moduleStructure,
  stateCorresponds := stateCorresponds,
  stateCoverage := hasCorrespondingState,
  implements := implements

end Silean.Examples.PicoRV.Control
