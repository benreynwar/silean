import Silean.Examples.PicoRV.ControlStructure
import Silean.Examples.PicoRV.Control.ControlBitLaws
import Silean.Examples.PicoRV.Control.ControlNextCertified
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.EqualsConstant.EqualsConstantCertified
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified
import Silean.Modules.Register.Register
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

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

/-! The sole structural state is the aggregate register. It corresponds to
the contract state exactly when the register's stored tuple is the packing of
those sixteen named fields. -/
private def stateCorresponds (contractState : cycleContract.state.Values)
    (structuralState : (certificationStructure layerChildren).State) : Prop :=
  (layerChildren .storage).certification.stateCorresponds
    (fun | .stored => stateMap.pack contractState)
    (structuralState .storage)

private theorem hasCorrespondingState
    (structuralState : (certificationStructure layerChildren).State) :
    ∃ contractState, stateCorresponds layerChildren contractState structuralState := by
  rcases (layerChildren .storage).certification.hasCorrespondingState
      (structuralState .storage) with ⟨storageState, storageCorresponds⟩
  refine ⟨stateMap.unpack (storageState .stored), ?_⟩
  change (layerChildren .storage).certification.stateCorresponds
    (fun | .stored => stateMap.pack (stateMap.unpack (storageState .stored)))
    (structuralState .storage)
  simpa using storageCorresponds

private theorem implements :
    Contracts.Cycle.Implements (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies

  have statelessMatch (child : Instance)
      [Subsingleton (childContracts child).state.Values]
      (state : (childContracts child).state.Values) :=
    childSolutionMatchesContract_of_subsingletonState layerChildren inputs
      structuralState proposal satisfies child state

  have inputsValueMatch :=
    statelessMatch .inputsValue SignalMap.emptyValues
  have stateFieldsMatch :=
    statelessMatch .stateFields SignalMap.emptyValues
  have nextMatch := statelessMatch .next SignalMap.emptyValues
  have fetchPhaseMatch := statelessMatch .fetchPhase SignalMap.emptyValues
  have emptyStateSubsingleton : Subsingleton emptySignalMap.Values := inferInstance
  have writePendingMatch :=
    letI : Subsingleton (childContracts .writePending).state.Values := by
      change Subsingleton emptySignalMap.Values
      exact emptyStateSubsingleton
    statelessMatch .writePending SignalMap.emptyValues
  have cpuregsWriteMatch :=
    letI : Subsingleton (childContracts .cpuregsWrite).state.Values := by
      change Subsingleton emptySignalMap.Values
      exact emptyStateSubsingleton
    statelessMatch .cpuregsWrite SignalMap.emptyValues
  have storageMatch := childSolutionMatchesContract layerChildren inputs
    structuralState proposal satisfies .storage
    (fun | .stored => stateMap.pack contractState) corresponds

  have inputsValueInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .inputsValue = (inputsOfValues inputs).toValues := by
    funext field
    cases field <;>
      simp [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.moduleInput, SignalSource.value, Inputs.toValues,
        inputsOfValues]
  have inputsValueValue : (proposal.2 .inputsValue).outputs .value =
      (inputsOfValues inputs).pack := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      ControlInputs.signalMap _ _ _).mp
      (inputsValueMatch.1.1 Modules.NamedTupleCombiner.Rule.apply)
    rw [inputsValueInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]
    rfl

  have storageOutputValue : (proposal.2 .storage).outputs .output =
      stateMap.pack contractState := by
    have equation := (Modules.Register.outputRule_holds_iff stateType _ _ _).mp
      (storageMatch.1.1 Primitives.RegisterRule.observe)
    exact equation
  have stateFieldsValue : (proposal.2 .stateFields).outputs = contractState := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      (stateFieldsMatch.1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [storageOutputValue] at equation
    simpa [splitValue_eq_unpack] using equation

  have nextValue : (proposal.2 .next).outputs .state =
      stateMap.pack (nextState (inputsOfValues inputs) contractState) := by
    have equation := (ControlNext.outputRule_holds_iff _ _ _).mp
      (nextMatch.1.1 ControlNext.Rule.apply)
    have nextInputs : ProposedValues.childInputs body
        (fun name => (layerChildren name).moduleStructure)
        inputs proposal.2 .next =
          (fun
            | .inputs => (inputsOfValues inputs).pack
            | .current => stateMap.pack contractState) := by
      funext input
      cases input <;>
        simp only [ProposedValues.childInputs_apply, body, wiring, context,
          EndpointContext.instanceOutput, SignalSource.value]
      · exact inputsValueValue
      · exact storageOutputValue
    rw [nextInputs] at equation
    simpa [ControlNext.outputState] using equation

  have fetchPhaseValue : (proposal.2 .fetchPhase).outputs .result =
      decide (phase contractState = cpuStateFetch) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 8 .bit) (stateBits cpuStateFetch) _ _ _).mp
      (fetchPhaseMatch.1.1 Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [stateFieldsValue] at equation
    rw [equalFetchState] at equation
    change (proposal.2 .fetchPhase).outputs .result =
      decide (phase contractState = cpuStateFetch) at equation
    exact equation
  have writePendingValue : (proposal.2 .writePending).outputs .output =
      ((contractState .latched_branch : Bool) || contractState .latched_store) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      (writePendingMatch.1.1 Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [stateFieldsValue] at equation
    exact equation
  have cpuregsWriteValue : (proposal.2 .cpuregsWrite).outputs .output =
      cpuregsWrite contractState := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      (cpuregsWriteMatch.1.1 Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [fetchPhaseValue, writePendingValue] at equation
    simpa [cpuregsWrite] using equation

  let nextContractState := stateRule.apply inputs contractState
  refine ⟨nextContractState, ?_, ?_⟩
  · constructor
    · intro rule
      cases rule
      rw [outputRule_holds_iff]
      funext output
      cases output
      · rw [show proposal.outputs .cpuregs_write =
            (proposal.2 .cpuregsWrite).outputs .output by
            exact satisfies.1 .cpuregs_write]
        exact cpuregsWriteValue
      · rw [show proposal.outputs .cpu_state =
            (proposal.2 .stateFields).outputs .cpu_state by
            exact satisfies.1 .cpu_state]
        exact congrFun stateFieldsValue .cpu_state
      · rw [show proposal.outputs .latched_store =
            (proposal.2 .stateFields).outputs .latched_store by
            exact satisfies.1 .latched_store]
        exact congrFun stateFieldsValue .latched_store
      · rw [show proposal.outputs .latched_stalu =
            (proposal.2 .stateFields).outputs .latched_stalu by
            exact satisfies.1 .latched_stalu]
        exact congrFun stateFieldsValue .latched_stalu
      · rw [show proposal.outputs .latched_branch =
            (proposal.2 .stateFields).outputs .latched_branch by
            exact satisfies.1 .latched_branch]
        exact congrFun stateFieldsValue .latched_branch
      · rw [show proposal.outputs .latched_is_lu =
            (proposal.2 .stateFields).outputs .latched_is_lu by
            exact satisfies.1 .latched_is_lu]
        exact congrFun stateFieldsValue .latched_is_lu
      · rw [show proposal.outputs .latched_is_lh =
            (proposal.2 .stateFields).outputs .latched_is_lh by
            exact satisfies.1 .latched_is_lh]
        exact congrFun stateFieldsValue .latched_is_lh
      · rw [show proposal.outputs .latched_is_lb =
            (proposal.2 .stateFields).outputs .latched_is_lb by
            exact satisfies.1 .latched_is_lb]
        exact congrFun stateFieldsValue .latched_is_lb
      · rw [show proposal.outputs .latched_rd =
            (proposal.2 .stateFields).outputs .latched_rd by
            exact satisfies.1 .latched_rd]
        exact congrFun stateFieldsValue .latched_rd
      · rw [show proposal.outputs .mem_wordsize =
            (proposal.2 .stateFields).outputs .mem_wordsize by
            exact satisfies.1 .mem_wordsize]
        exact congrFun stateFieldsValue .mem_wordsize
      · rw [show proposal.outputs .mem_do_prefetch =
            (proposal.2 .stateFields).outputs .mem_do_prefetch by
            exact satisfies.1 .mem_do_prefetch]
        exact congrFun stateFieldsValue .mem_do_prefetch
      · rw [show proposal.outputs .mem_do_rinst =
            (proposal.2 .stateFields).outputs .mem_do_rinst by
            exact satisfies.1 .mem_do_rinst]
        exact congrFun stateFieldsValue .mem_do_rinst
      · rw [show proposal.outputs .mem_do_rdata =
            (proposal.2 .stateFields).outputs .mem_do_rdata by
            exact satisfies.1 .mem_do_rdata]
        exact congrFun stateFieldsValue .mem_do_rdata
      · rw [show proposal.outputs .mem_do_wdata =
            (proposal.2 .stateFields).outputs .mem_do_wdata by
            exact satisfies.1 .mem_do_wdata]
        exact congrFun stateFieldsValue .mem_do_wdata
      · rw [show proposal.outputs .decoder_trigger =
            (proposal.2 .stateFields).outputs .decoder_trigger by
            exact satisfies.1 .decoder_trigger]
        exact congrFun stateFieldsValue .decoder_trigger
      · rw [show proposal.outputs .decoder_pseudo_trigger =
            (proposal.2 .stateFields).outputs .decoder_pseudo_trigger by
            exact satisfies.1 .decoder_pseudo_trigger]
        exact congrFun stateFieldsValue .decoder_pseudo_trigger
      · rw [show proposal.outputs .trap =
            (proposal.2 .stateFields).outputs .trap by
            exact satisfies.1 .trap]
        exact congrFun stateFieldsValue .trap
    · rfl
  · change (layerChildren .storage).certification.stateCorresponds
      (fun | .stored => stateMap.pack nextContractState)
      (proposal.2 .storage).nextState
    rw [show (fun _ => stateMap.pack nextContractState) =
        (childContracts .storage).stateRule.apply
          (ProposedValues.childInputs body
            (fun child => (layerChildren child).moduleStructure)
            inputs proposal.2 .storage)
          (fun _ => stateMap.pack contractState) by
      funext storageState
      cases storageState
      change stateMap.pack (nextState (inputsOfValues inputs) contractState) =
        (proposal.2 .next).outputs .state
      exact nextValue.symm]
    exact storageMatch.2

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

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.Control
