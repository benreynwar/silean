import Silean.Examples.PicoRV.MemoryStructure
import Silean.Examples.PicoRV.Memory.MemoryLookaheadCertified
import Silean.Examples.PicoRV.Memory.MemoryNextCertified
import Silean.Examples.PicoRV.Memory.MemoryReadFormattingCertified
import Silean.Examples.PicoRV.Memory.MemoryResponseCertified
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified
import Silean.Modules.Register.Register

namespace Silean.Examples.PicoRV.Memory

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

set_option maxRecDepth 4096

module_child_certifications childContracts for body where
  inputsValue := Modules.NamedTupleCombiner.certification MemoryInputs.signalMap,
  storage := Modules.Register.certification stateType,
  stateFields := Modules.NamedTupleSplitter.certification stateMap,
  lookahead := Lookahead.certification,
  readFormatting := ReadFormatting.certification,
  response := Response.certification,
  next := Next.certification

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .registered => [
        .storage => Primitives.RegisterRule.observe,
        .stateFields => Modules.NamedTupleSplitter.Rule.apply]
    | .memLaRead => [
        .storage => Primitives.RegisterRule.observe,
        .lookahead => Lookahead.Rule.memLaRead]
    | .memLaWrite => [
        .storage => Primitives.RegisterRule.observe,
        .lookahead => Lookahead.Rule.memLaWrite]
    | .memLaAddr => [.lookahead => Lookahead.Rule.memLaAddr]
    | .memLaWdata => [.lookahead => Lookahead.Rule.memLaWdata]
    | .memLaWstrb => [.lookahead => Lookahead.Rule.memLaWstrb]
    | .memDone => [
        .storage => Primitives.RegisterRule.observe,
        .response => Response.Rule.done]
    | .memRdataWord => [.readFormatting => ReadFormatting.Rule.apply]
    | .memRdataLatched => [
        .storage => Primitives.RegisterRule.observe,
        .response => Response.Rule.data]
    | .memRdataQ => [
        .storage => Primitives.RegisterRule.observe,
        .stateFields => Modules.NamedTupleSplitter.Rule.apply]
  state := [
    .inputsValue => Modules.NamedTupleCombiner.Rule.apply,
    .storage => Primitives.RegisterRule.observe,
    .next => Next.Rule.apply]

section LayerCertification

variable (layerChildren : ChildStructures body childContracts)

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

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
    Contracts.Cycle.Implements (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies

  have statelessMatch (child : Instance)
      [Subsingleton (childContracts child).state.Values]
      (state : (childContracts child).state.Values) :=
    childSolutionMatchesContract_of_subsingletonState layerChildren inputs
      structuralState proposal satisfies child state
  have inputsValueMatch := statelessMatch .inputsValue SignalMap.emptyValues
  have stateFieldsMatch := statelessMatch .stateFields SignalMap.emptyValues
  have lookaheadMatch := statelessMatch .lookahead SignalMap.emptyValues
  have readFormattingMatch := statelessMatch .readFormatting SignalMap.emptyValues
  have responseMatch := statelessMatch .response SignalMap.emptyValues
  have nextMatch := statelessMatch .next SignalMap.emptyValues
  have storageMatch := childSolutionMatchesContract layerChildren inputs
    structuralState proposal satisfies .storage
    (fun | .stored => stateMap.pack contractState) corresponds

  let memoryInputs := inputsOfValues inputs
  have inputsValueInputs : ProposedValues.childInputs body
      (fun name => (layerChildren name).moduleStructure)
      inputs proposal.2 .inputsValue = memoryInputs.toValues := by
    funext field
    cases field <;>
      simp [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.moduleInput, SignalSource.value, Inputs.toValues,
        memoryInputs, inputsOfValues]
  have inputsValueValue : (proposal.2 .inputsValue).outputs .value =
      memoryInputs.pack := by
    have equation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      MemoryInputs.signalMap _ _ _).mp
      (inputsValueMatch.1.1 Modules.NamedTupleCombiner.Rule.apply)
    rw [inputsValueInputs] at equation
    rw [equation, Modules.NamedTupleCombiner.combinedValue_eq_pack]
    rfl
  have storageOutputValue : (proposal.2 .storage).outputs .output =
      stateMap.pack contractState := by
    exact (Modules.Register.outputRule_holds_iff stateType _ _ _).mp
      (storageMatch.1.1 Primitives.RegisterRule.observe)
  have stateFieldsValue : (proposal.2 .stateFields).outputs = contractState := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      (stateFieldsMatch.1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [storageOutputValue] at equation
    simpa [ProofSupport.splitValue_eq_unpack] using equation

  have lookaheadReadValue : (proposal.2 .lookahead).outputs .mem_la_read =
      memLaReadFrom (inputs .resetn) (inputs .mem_do_prefetch)
        (inputs .mem_do_rinst) (inputs .mem_do_rdata) contractState := by
    have equation := (Lookahead.memLaReadRule_holds_iff _ _ _).mp
      (lookaheadMatch.1.1 Lookahead.Rule.memLaRead)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [storageOutputValue] at equation
    simpa [Lookahead.readValue] using equation
  have lookaheadWriteValue : (proposal.2 .lookahead).outputs .mem_la_write =
      memLaWriteFrom (inputs .resetn) (inputs .mem_do_wdata) contractState := by
    have equation := (Lookahead.memLaWriteRule_holds_iff _ _ _).mp
      (lookaheadMatch.1.1 Lookahead.Rule.memLaWrite)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [storageOutputValue] at equation
    simpa [Lookahead.writeValue] using equation
  have lookaheadAddrValue : (proposal.2 .lookahead).outputs .mem_la_addr =
      memLaAddrFrom (inputs .mem_do_prefetch) (inputs .mem_do_rinst)
        (inputs .next_pc) (inputs .reg_op1) := by
    have equation := (Lookahead.memLaAddrRule_holds_iff _ _ _).mp
      (lookaheadMatch.1.1 Lookahead.Rule.memLaAddr)
    normalize_child_hyp equation unfolding body, wiring, context
    exact equation
  have lookaheadWdataValue : (proposal.2 .lookahead).outputs .mem_la_wdata =
      formattedWriteDataFrom (inputs .mem_wordsize) (inputs .reg_op2) := by
    have equation := (Lookahead.memLaWdataRule_holds_iff _ _ _).mp
      (lookaheadMatch.1.1 Lookahead.Rule.memLaWdata)
    normalize_child_hyp equation unfolding body, wiring, context
    exact equation
  have lookaheadWstrbValue : (proposal.2 .lookahead).outputs .mem_la_wstrb =
      formattedWriteMaskFrom (inputs .mem_wordsize) (inputs .reg_op1) := by
    have equation := (Lookahead.memLaWstrbRule_holds_iff _ _ _).mp
      (lookaheadMatch.1.1 Lookahead.Rule.memLaWstrb)
    normalize_child_hyp equation unfolding body, wiring, context
    exact equation

  have readFormattingValue :
      (proposal.2 .readFormatting).outputs .mem_rdata_word =
        formattedReadDataFrom (inputs .mem_wordsize) (inputs .reg_op1)
          (inputs .mem_rdata) := by
    have equation := (ReadFormatting.outputRule_holds_iff _ _ _).mp
      (readFormattingMatch.1.1 ReadFormatting.Rule.apply)
    simp only [ReadFormatting.outputValue] at equation
    normalize_child_hyp equation unfolding body, wiring, context
    exact equation

  have responseDoneValue : (proposal.2 .response).outputs .mem_done =
      memDoneFrom (inputs .resetn) (inputs .mem_do_rinst)
        (inputs .mem_do_rdata) (inputs .mem_do_wdata) (inputs .mem_ready)
        contractState := by
    have equation := (Response.doneRule_holds_iff _ _ _).mp
      (responseMatch.1.1 Response.Rule.done)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [storageOutputValue] at equation
    simpa [Response.doneValue] using equation
  have responseDataValue : (proposal.2 .response).outputs .mem_rdata_latched =
      memRdataLatchedFrom (inputs .mem_ready) (inputs .mem_rdata)
        contractState := by
    have equation := (Response.dataRule_holds_iff _ _ _).mp
      (responseMatch.1.1 Response.Rule.data)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [storageOutputValue] at equation
    exact equation

  have nextValue : (proposal.2 .next).outputs .state =
      stateMap.pack (nextState memoryInputs contractState) := by
    have equation := (Next.outputRule_holds_iff _ _ _).mp
      (nextMatch.1.1 Next.Rule.apply)
    have nextInputs : ProposedValues.childInputs body
        (fun name => (layerChildren name).moduleStructure)
        inputs proposal.2 .next = (fun
          | .inputs => memoryInputs.pack
          | .current => stateMap.pack contractState) := by
      funext input
      cases input
      · simpa only [ProposedValues.childInputs_apply, body, wiring, context,
          EndpointContext.instanceOutput, SignalSource.value] using inputsValueValue
      · change (proposal.2 .storage).outputs .output =
          stateMap.pack contractState
        exact storageOutputValue
    rw [nextInputs] at equation
    simpa [Next.outputState, memoryInputs] using equation

  let nextContractState := stateRule.apply inputs contractState
  refine ⟨nextContractState, ?_, ?_⟩
  · constructor
    · intro rule
      cases rule
      · rw [registeredRule_holds_iff]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [show proposal.outputs .mem_valid =
              (proposal.2 .stateFields).outputs .mem_valid by
            exact satisfies.1 .mem_valid]
          exact congrFun stateFieldsValue .mem_valid
        · rw [show proposal.outputs .mem_instr =
              (proposal.2 .stateFields).outputs .mem_instr by
            exact satisfies.1 .mem_instr]
          exact congrFun stateFieldsValue .mem_instr
        · rw [show proposal.outputs .mem_addr =
              (proposal.2 .stateFields).outputs .mem_addr by
            exact satisfies.1 .mem_addr]
          exact congrFun stateFieldsValue .mem_addr
        · rw [show proposal.outputs .mem_wdata =
              (proposal.2 .stateFields).outputs .mem_wdata by
            exact satisfies.1 .mem_wdata]
          exact congrFun stateFieldsValue .mem_wdata
        · rw [show proposal.outputs .mem_wstrb =
              (proposal.2 .stateFields).outputs .mem_wstrb by
            exact satisfies.1 .mem_wstrb]
          exact congrFun stateFieldsValue .mem_wstrb
      · rw [memLaReadRule_holds_iff]
        rw [show proposal.outputs .mem_la_read =
            (proposal.2 .lookahead).outputs .mem_la_read by
          exact satisfies.1 .mem_la_read]
        exact lookaheadReadValue
      · rw [memLaWriteRule_holds_iff]
        rw [show proposal.outputs .mem_la_write =
            (proposal.2 .lookahead).outputs .mem_la_write by
          exact satisfies.1 .mem_la_write]
        exact lookaheadWriteValue
      · rw [memLaAddrRule_holds_iff]
        rw [show proposal.outputs .mem_la_addr =
            (proposal.2 .lookahead).outputs .mem_la_addr by
          exact satisfies.1 .mem_la_addr]
        exact lookaheadAddrValue
      · rw [memLaWdataRule_holds_iff]
        rw [show proposal.outputs .mem_la_wdata =
            (proposal.2 .lookahead).outputs .mem_la_wdata by
          exact satisfies.1 .mem_la_wdata]
        exact lookaheadWdataValue
      · rw [memLaWstrbRule_holds_iff]
        rw [show proposal.outputs .mem_la_wstrb =
            (proposal.2 .lookahead).outputs .mem_la_wstrb by
          exact satisfies.1 .mem_la_wstrb]
        exact lookaheadWstrbValue
      · rw [memDoneRule_holds_iff]
        rw [show proposal.outputs .mem_done =
            (proposal.2 .response).outputs .mem_done by
          exact satisfies.1 .mem_done]
        exact responseDoneValue
      · rw [memRdataWordRule_holds_iff]
        rw [show proposal.outputs .mem_rdata_word =
            (proposal.2 .readFormatting).outputs .mem_rdata_word by
          exact satisfies.1 .mem_rdata_word]
        exact readFormattingValue
      · rw [memRdataLatchedRule_holds_iff]
        rw [show proposal.outputs .mem_rdata_latched =
            (proposal.2 .response).outputs .mem_rdata_latched by
          exact satisfies.1 .mem_rdata_latched]
        exact responseDataValue
      · rw [memRdataQRule_holds_iff]
        rw [show proposal.outputs .mem_rdata_q =
            (proposal.2 .stateFields).outputs .mem_rdata_q by
          exact satisfies.1 .mem_rdata_q]
        exact congrFun stateFieldsValue .mem_rdata_q
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
      change stateMap.pack (nextState memoryInputs contractState) =
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

end Silean.Examples.PicoRV.Memory
