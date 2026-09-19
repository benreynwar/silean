import PicoRV.Internal.MemoryStructure
import PicoRV.Memory.Internal.MemoryLookaheadVerification
import PicoRV.Memory.Internal.MemoryNextVerification
import PicoRV.Memory.Internal.MemoryReadFormattingVerification
import PicoRV.Memory.Internal.MemoryResponseVerification
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems
import Silean.Modules.Register.RegisterTheorems

namespace PicoRV.Memory

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

set_option maxRecDepth 4096

module_child_certifications childContracts for body where
  inputsValue := Silean.Modules.NamedTupleCombiner.certification MemoryInputs.signalMap,
  storage := Silean.Modules.Register.certification stateType,
  stateFields := Silean.Modules.NamedTupleSplitter.certification stateMap,
  lookahead := Lookahead.certification,
  readFormatting := ReadFormatting.certification,
  response := Response.certification,
  next := Next.certification

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .registered => [
        .storage => Silean.Primitives.RegisterRule.observe,
        .stateFields => Silean.Modules.NamedTupleSplitter.Rule.apply]
    | .memLaRead => [
        .storage => Silean.Primitives.RegisterRule.observe,
        .lookahead => Lookahead.Rule.memLaRead]
    | .memLaWrite => [
        .storage => Silean.Primitives.RegisterRule.observe,
        .lookahead => Lookahead.Rule.memLaWrite]
    | .memLaAddr => [.lookahead => Lookahead.Rule.memLaAddr]
    | .memLaWdata => [.lookahead => Lookahead.Rule.memLaWdata]
    | .memLaWstrb => [.lookahead => Lookahead.Rule.memLaWstrb]
    | .memDone => [
        .storage => Silean.Primitives.RegisterRule.observe,
        .response => Response.Rule.done]
    | .memRdataWord => [.readFormatting => ReadFormatting.Rule.apply]
    | .memRdataLatched => [
        .storage => Silean.Primitives.RegisterRule.observe,
        .response => Response.Rule.data]
    | .memRdataQ => [
        .storage => Silean.Primitives.RegisterRule.observe,
        .stateFields => Silean.Modules.NamedTupleSplitter.Rule.apply]
  state := [
    .inputsValue => Silean.Modules.NamedTupleCombiner.Rule.apply,
    .storage => Silean.Primitives.RegisterRule.observe,
    .next => Next.Rule.apply]

section LayerCertification

variable (layerChildren : ChildStructures body childContracts)

private abbrev certificationStructure :=
  Silean.Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

/-! The sole sequential state is the aggregate register. Its stored tuple is
the exact packing of the seven named fields in the behavioral contract. -/
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
    Silean.Contracts.Cycle.ImplementsSolutions (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  let inputs := hierStep.inputs

  have coveredMatch (child : Instance) :=
    (childSolutionMatchesCoveredContract layerChildren hierStep
      satisfies child).choose_spec
  have inputsValueMatch := coveredMatch .inputsValue
  have stateFieldsMatch := coveredMatch .stateFields
  have lookaheadMatch := coveredMatch .lookahead
  have readFormattingMatch := coveredMatch .readFormatting
  have responseMatch := coveredMatch .response
  have nextMatch := coveredMatch .next
  have storageMatch := childSolutionMatchesContract layerChildren hierStep
    satisfies .storage
    (fun | .stored => stateMap.pack contractState) corresponds

  let memoryInputs := inputsOfValues inputs
  have inputsValueInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .inputsValue = memoryInputs.toValues := by
    funext field
    cases field <;> rfl
  have inputsValueValue : hierStep.childOutputs .inputsValue .value =
      memoryInputs.pack := by
    have equation := (Silean.Modules.NamedTupleCombiner.outputRule_holds_iff
      MemoryInputs.signalMap _ _ _).mp
      (inputsValueMatch.ruleHolds Silean.Modules.NamedTupleCombiner.Rule.apply)
    rw [inputsValueInputs] at equation
    rw [equation, Silean.Modules.NamedTupleCombiner.combinedValue_eq_pack]
    rfl
  have storageOutputValue : hierStep.childOutputs .storage .output =
      stateMap.pack contractState := by
    exact (Silean.Modules.Register.outputRule_holds_iff stateType _ _ _).mp
      (storageMatch.ruleHolds Silean.Primitives.RegisterRule.observe)
  have stateFieldsValue : hierStep.childOutputs .stateFields = contractState := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      (stateFieldsMatch.ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    rw [storageOutputValue] at equation
    simpa [ProofSupport.splitValue_eq_unpack] using equation

  have lookaheadReadValue : hierStep.childOutputs .lookahead .mem_la_read =
      memLaReadFrom (inputs .resetn) (inputs .mem_do_prefetch)
        (inputs .mem_do_rinst) (inputs .mem_do_rdata) contractState := by
    have equation := (Lookahead.memLaReadRule_holds_iff _ _ _).mp
      (lookaheadMatch.ruleHolds Lookahead.Rule.memLaRead)
    normalize_child_hyp equation unfolding wiring, context
    rw [storageOutputValue] at equation
    simpa [Lookahead.readValue] using equation
  have lookaheadWriteValue : hierStep.childOutputs .lookahead .mem_la_write =
      memLaWriteFrom (inputs .resetn) (inputs .mem_do_wdata) contractState := by
    have equation := (Lookahead.memLaWriteRule_holds_iff _ _ _).mp
      (lookaheadMatch.ruleHolds Lookahead.Rule.memLaWrite)
    normalize_child_hyp equation unfolding wiring, context
    rw [storageOutputValue] at equation
    simpa [Lookahead.writeValue] using equation
  have lookaheadAddrValue : hierStep.childOutputs .lookahead .mem_la_addr =
      memLaAddrFrom (inputs .mem_do_prefetch) (inputs .mem_do_rinst)
        (inputs .next_pc) (inputs .reg_op1) := by
    have equation := (Lookahead.memLaAddrRule_holds_iff _ _ _).mp
      (lookaheadMatch.ruleHolds Lookahead.Rule.memLaAddr)
    normalize_child_hyp equation unfolding wiring, context
    exact equation
  have lookaheadWdataValue : hierStep.childOutputs .lookahead .mem_la_wdata =
      formattedWriteDataFrom (inputs .mem_wordsize) (inputs .reg_op2) := by
    have equation := (Lookahead.memLaWdataRule_holds_iff _ _ _).mp
      (lookaheadMatch.ruleHolds Lookahead.Rule.memLaWdata)
    normalize_child_hyp equation unfolding wiring, context
    exact equation
  have lookaheadWstrbValue : hierStep.childOutputs .lookahead .mem_la_wstrb =
      formattedWriteMaskFrom (inputs .mem_wordsize) (inputs .reg_op1) := by
    have equation := (Lookahead.memLaWstrbRule_holds_iff _ _ _).mp
      (lookaheadMatch.ruleHolds Lookahead.Rule.memLaWstrb)
    normalize_child_hyp equation unfolding wiring, context
    exact equation

  have readFormattingValue :
      hierStep.childOutputs .readFormatting .mem_rdata_word =
        formattedReadDataFrom (inputs .mem_wordsize) (inputs .reg_op1)
          (inputs .mem_rdata) := by
    have equation := (ReadFormatting.outputRule_holds_iff _ _ _).mp
      (readFormattingMatch.ruleHolds ReadFormatting.Rule.apply)
    simp only [ReadFormatting.outputValue] at equation
    normalize_child_hyp equation unfolding wiring, context
    exact equation

  have responseDoneValue : hierStep.childOutputs .response .mem_done =
      memDoneFrom (inputs .resetn) (inputs .mem_do_rinst)
        (inputs .mem_do_rdata) (inputs .mem_do_wdata) (inputs .mem_ready)
        contractState := by
    have equation := (Response.doneRule_holds_iff _ _ _).mp
      (responseMatch.ruleHolds Response.Rule.done)
    normalize_child_hyp equation unfolding wiring, context
    rw [storageOutputValue] at equation
    simpa [Response.doneValue] using equation
  have responseDataValue : hierStep.childOutputs .response .mem_rdata_latched =
      memRdataLatchedFrom (inputs .mem_ready) (inputs .mem_rdata)
        contractState := by
    have equation := (Response.dataRule_holds_iff _ _ _).mp
      (responseMatch.ruleHolds Response.Rule.data)
    normalize_child_hyp equation unfolding wiring, context
    rw [storageOutputValue] at equation
    exact equation

  have nextValue : hierStep.childOutputs .next .state =
      stateMap.pack (nextState memoryInputs contractState) := by
    have equation := (Next.outputRule_holds_iff _ _ _).mp
      (nextMatch.ruleHolds Next.Rule.apply)
    have nextInputs : body.wiring.childInputValues hierStep.inputs
      hierStep.childOutputs .next = (fun
          | .inputs => memoryInputs.pack
          | .current => stateMap.pack contractState) := by
      funext input
      cases input
      · change hierStep.childOutputs .inputsValue .value = _
        exact inputsValueValue
      · change hierStep.childOutputs .storage .output =
          stateMap.pack contractState
        exact storageOutputValue
    rw [nextInputs] at equation
    simpa [Next.outputState, memoryInputs] using equation

  let nextContractState := stateRule.apply inputs contractState
  refine ⟨nextContractState, ?_, ?_⟩
  · constructor
    · intro rule
      dsimp only
      cases rule
      · rw [registeredRule_holds_iff]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [show hierStep.outputs .mem_valid =
              hierStep.childOutputs .stateFields .mem_valid by
            exact satisfies.1 .mem_valid]
          exact congrFun stateFieldsValue .mem_valid
        · rw [show hierStep.outputs .mem_instr =
              hierStep.childOutputs .stateFields .mem_instr by
            exact satisfies.1 .mem_instr]
          exact congrFun stateFieldsValue .mem_instr
        · rw [show hierStep.outputs .mem_addr =
              hierStep.childOutputs .stateFields .mem_addr by
            exact satisfies.1 .mem_addr]
          exact congrFun stateFieldsValue .mem_addr
        · rw [show hierStep.outputs .mem_wdata =
              hierStep.childOutputs .stateFields .mem_wdata by
            exact satisfies.1 .mem_wdata]
          exact congrFun stateFieldsValue .mem_wdata
        · rw [show hierStep.outputs .mem_wstrb =
              hierStep.childOutputs .stateFields .mem_wstrb by
            exact satisfies.1 .mem_wstrb]
          exact congrFun stateFieldsValue .mem_wstrb
      · rw [memLaReadRule_holds_iff]
        rw [show hierStep.outputs .mem_la_read =
            hierStep.childOutputs .lookahead .mem_la_read by
          exact satisfies.1 .mem_la_read]
        exact lookaheadReadValue
      · rw [memLaWriteRule_holds_iff]
        rw [show hierStep.outputs .mem_la_write =
            hierStep.childOutputs .lookahead .mem_la_write by
          exact satisfies.1 .mem_la_write]
        exact lookaheadWriteValue
      · rw [memLaAddrRule_holds_iff]
        rw [show hierStep.outputs .mem_la_addr =
            hierStep.childOutputs .lookahead .mem_la_addr by
          exact satisfies.1 .mem_la_addr]
        exact lookaheadAddrValue
      · rw [memLaWdataRule_holds_iff]
        rw [show hierStep.outputs .mem_la_wdata =
            hierStep.childOutputs .lookahead .mem_la_wdata by
          exact satisfies.1 .mem_la_wdata]
        exact lookaheadWdataValue
      · rw [memLaWstrbRule_holds_iff]
        rw [show hierStep.outputs .mem_la_wstrb =
            hierStep.childOutputs .lookahead .mem_la_wstrb by
          exact satisfies.1 .mem_la_wstrb]
        exact lookaheadWstrbValue
      · rw [memDoneRule_holds_iff]
        rw [show hierStep.outputs .mem_done =
            hierStep.childOutputs .response .mem_done by
          exact satisfies.1 .mem_done]
        exact responseDoneValue
      · rw [memRdataWordRule_holds_iff]
        rw [show hierStep.outputs .mem_rdata_word =
            hierStep.childOutputs .readFormatting .mem_rdata_word by
          exact satisfies.1 .mem_rdata_word]
        exact readFormattingValue
      · rw [memRdataLatchedRule_holds_iff]
        rw [show hierStep.outputs .mem_rdata_latched =
            hierStep.childOutputs .response .mem_rdata_latched by
          exact satisfies.1 .mem_rdata_latched]
        exact responseDataValue
      · rw [memRdataQRule_holds_iff]
        rw [show hierStep.outputs .mem_rdata_q =
            hierStep.childOutputs .stateFields .mem_rdata_q by
          exact satisfies.1 .mem_rdata_q]
        exact congrFun stateFieldsValue .mem_rdata_q
    · rfl
  · change (layerChildren .storage).certification.stateCorresponds
      (fun | .stored => stateMap.pack nextContractState)
      (Silean.HierStep.nextState (layerChildren .storage).moduleStructure
        (hierStep.children .storage))
    rw [show (fun _ => stateMap.pack nextContractState) =
        (childContracts .storage).stateRule.apply
          (body.wiring.childInputValues hierStep.inputs
            hierStep.childOutputs .storage)
          (fun _ => stateMap.pack contractState) by
      funext storageState
      cases storageState
      change stateMap.pack (nextState memoryInputs contractState) =
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

end PicoRV.Memory
