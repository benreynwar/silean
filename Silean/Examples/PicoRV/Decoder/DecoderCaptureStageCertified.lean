import Silean.Examples.PicoRV.Decoder.DecoderCaptureStage
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Modules.EnabledRegister.EnabledRegisterCertified
import Silean.Modules.EnabledResetRegister.EnabledResetRegisterCertified
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified
import Silean.Modules.VectorLayout.VectorLayoutCertified
import Silean.Primitives.Not

namespace Silean.Examples.PicoRV.Decoder.CaptureStage

open Silean
open Silean.Authoring
open Silean.Examples.PicoRV.Decoder
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  captureEnable := Primitives.andCertified.certification,
  reset := Primitives.notCertified.certification,
  opcode := Modules.VectorSlice.certification .bit 0 7 25,
  funct3 := Modules.VectorSlice.certification .bit 12 3 17,
  decodedRd := Modules.VectorSlice.certification .bit 7 5 20,
  decodedRs1 := Modules.VectorSlice.certification .bit 15 5 12,
  decodedRs2 := Modules.VectorSlice.certification .bit 20 5 7,
  opcodeLui := Modules.EqualsConstant.certification (.vector 7 .bit) (bits 7 0x37),
  opcodeAuipc := Modules.EqualsConstant.certification (.vector 7 .bit) (bits 7 0x17),
  opcodeJal := Modules.EqualsConstant.certification (.vector 7 .bit) (bits 7 0x6f),
  opcodeJalr := Modules.EqualsConstant.certification (.vector 7 .bit) (bits 7 0x67),
  opcodeBranch := Modules.EqualsConstant.certification (.vector 7 .bit) (bits 7 0x63),
  opcodeLoad := Modules.EqualsConstant.certification (.vector 7 .bit) (bits 7 0x03),
  opcodeStore := Modules.EqualsConstant.certification (.vector 7 .bit) (bits 7 0x23),
  opcodeAluImm := Modules.EqualsConstant.certification (.vector 7 .bit) (bits 7 0x13),
  opcodeAluReg := Modules.EqualsConstant.certification (.vector 7 .bit) (bits 7 0x33),
  funct3Zero := Modules.EqualsConstant.certification (.vector 3 .bit) (bits 3 0),
  jalr := Primitives.andCertified.certification,
  zero := Modules.Constant.certification .bit false,
  immediate := Modules.VectorLayout.certification 32 32 immediateJLayout,
  storedNext := Modules.NamedTupleCombiner.certification storedMap,
  stored := Modules.EnabledRegister.certification storedType,
  storedOutputs := Modules.NamedTupleSplitter.certification storedMap,
  branch := Modules.EnabledResetRegister.certification .bit false

/-! ## Structural schedules -/

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .outputs => [.stored => Modules.EnabledRegister.Rule.observe,
      .storedOutputs => Modules.NamedTupleAdapterRule.apply,
      .branch => Modules.EnabledResetRegister.Rule.observe]
  state := [.captureEnable => Primitives.AndRule.apply,
    .reset => Primitives.NotRule.apply,
    {.opcode, .funct3, .decodedRd, .decodedRs1, .decodedRs2} =>
      Modules.VectorSlice.Rule.apply,
    .zero => Primitives.ConstantRule.apply,
    {.opcodeLui, .opcodeAuipc, .opcodeJal, .opcodeJalr, .opcodeBranch,
      .opcodeLoad, .opcodeStore, .opcodeAluImm, .opcodeAluReg, .funct3Zero} =>
      Modules.Equality.Rule.apply,
    .jalr => Primitives.AndRule.apply,
    .immediate => Modules.VectorLayout.Rule.apply,
    .storedNext => Modules.NamedTupleAdapterRule.apply]

/-! ## Cycle certification -/

private def storedValues (state : stateMap.Values) : storedMap.Values :=
  fun
  | .instr_lui => state .instr_lui
  | .instr_auipc => state .instr_auipc
  | .instr_jal => state .instr_jal
  | .instr_jalr => state .instr_jalr
  | .decoded_rd => state .decoded_rd
  | .decoded_rs1 => state .decoded_rs1
  | .decoded_rs2 => state .decoded_rs2
  | .decoded_imm_j => state .decoded_imm_j
  | .compressed_instr => state .compressed_instr
  | .is_lb_lh_lw_lbu_lhu => state .is_lb_lh_lw_lbu_lhu
  | .is_sb_sh_sw => state .is_sb_sh_sw
  | .is_alu_reg_imm => state .is_alu_reg_imm
  | .is_alu_reg_reg => state .is_alu_reg_reg

private def storedValue (state : stateMap.Values) : storedType.Denote :=
  storedMap.pack (storedValues state)

private def captureValues (inputs : Inputs) : storedMap.Values :=
  let word := inputs.mem_rdata_latched
  fun
  | .instr_lui => matchesBits 7 0x37 (opcodeBits word)
  | .instr_auipc => matchesBits 7 0x17 (opcodeBits word)
  | .instr_jal => matchesBits 7 0x6f (opcodeBits word)
  | .instr_jalr =>
      matchesBits 7 0x67 (opcodeBits word) && matchesBits 3 0 (funct3Bits word)
  | .decoded_rd => addressBits 7 20 word
  | .decoded_rs1 => addressBits 15 12 word
  | .decoded_rs2 => addressBits 20 7 word
  | .decoded_imm_j => immediateJBits word
  | .compressed_instr => false
  | .is_lb_lh_lw_lbu_lhu => matchesBits 7 0x03 (opcodeBits word)
  | .is_sb_sh_sw => matchesBits 7 0x23 (opcodeBits word)
  | .is_alu_reg_imm => matchesBits 7 0x13 (opcodeBits word)
  | .is_alu_reg_reg => matchesBits 7 0x33 (opcodeBits word)

private def captureData (inputs : Inputs) : storedType.Denote :=
  storedMap.pack (captureValues inputs)

private theorem storedValue_captured (inputs : Inputs) (state : stateMap.Values) :
    storedValue (captured inputs state) =
      bif (inputs.mem_do_rinst && inputs.mem_done)
        then captureData inputs else storedValue state := by
  rcases inputs with ⟨resetn, memDoRinst, memDone, word⟩
  cases memDoRinst <;> cases memDone <;>
    simp [captured, storedValue, captureData]
  apply congrArg storedMap.pack
  funext field
  cases field <;>
    simp [storedValues, captureValues, stateMap,
      SignalMap.set]

private theorem branch_nextState (inputs : Inputs) (state : stateMap.Values) :
    nextState inputs state .is_beq_bne_blt_bge_bltu_bgeu =
      bif !inputs.resetn then false
      else bif (inputs.mem_do_rinst && inputs.mem_done)
        then matchesBits 7 0x63 (opcodeBits inputs.mem_rdata_latched)
        else state .is_beq_bne_blt_bge_bltu_bgeu := by
  rcases inputs with ⟨resetn, memDoRinst, memDone, word⟩
  cases resetn <;> cases memDoRinst <;> cases memDone <;>
    simp [nextState, captured, SignalMap.set]

private theorem storedValue_nextState (inputs : Inputs) (state : stateMap.Values) :
    storedValue (nextState inputs state) = storedValue (captured inputs state) := by
  rcases inputs with ⟨resetn, memDoRinst, memDone, word⟩
  cases resetn <;> simp [nextState, storedValue]
  apply congrArg storedMap.pack
  funext field
  cases field <;>
    simp [storedValues, stateMap, SignalMap.set]

private def storedContractState (state : stateMap.Values) :
    (Modules.EnabledRegister.cycleContract storedType).state.Values :=
  fun | .stored => storedValue state

private def branchContractState (state : stateMap.Values) :
    (Modules.EnabledResetRegister.cycleContract .bit false).state.Values :=
  fun | .stored => state .is_beq_bne_blt_bge_bltu_bgeu

private def mergeStoredState (stored : storedType.Denote) (branch : Bool) :
    stateMap.Values :=
  let values := storedMap.unpack stored
  fun
  | .instr_lui => values .instr_lui
  | .instr_auipc => values .instr_auipc
  | .instr_jal => values .instr_jal
  | .instr_jalr => values .instr_jalr
  | .decoded_rd => values .decoded_rd
  | .decoded_rs1 => values .decoded_rs1
  | .decoded_rs2 => values .decoded_rs2
  | .decoded_imm_j => values .decoded_imm_j
  | .compressed_instr => values .compressed_instr
  | .is_beq_bne_blt_bge_bltu_bgeu => branch
  | .is_lb_lh_lw_lbu_lhu => values .is_lb_lh_lw_lbu_lhu
  | .is_sb_sh_sw => values .is_sb_sh_sw
  | .is_alu_reg_imm => values .is_alu_reg_imm
  | .is_alu_reg_reg => values .is_alu_reg_reg

@[simp] private theorem storedValue_mergeStoredState (stored : storedType.Denote)
    (branch : Bool) : storedValue (mergeStoredState stored branch) = stored := by
  unfold storedValue
  rw [show storedValues (mergeStoredState stored branch) = storedMap.unpack stored by
    funext field
    cases field <;> rfl]
  exact storedMap.pack_unpack stored

section Certification

variable (layerChildren : ChildStructures body childContracts)

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (contractState : stateMap.Values)
    (structuralState : (certificationStructure layerChildren).State) : Prop :=
  (layerChildren .stored).certification.stateCorresponds
      (storedContractState contractState) (structuralState .stored) ∧
    (layerChildren .branch).certification.stateCorresponds
      (branchContractState contractState) (structuralState .branch)

private theorem hasCorrespondingState
    (structuralState : (certificationStructure layerChildren).State) :
    ∃ contractState, stateCorresponds layerChildren contractState structuralState := by
  rcases (layerChildren .stored).certification.hasCorrespondingState
      (structuralState .stored) with ⟨stored, storedCorresponds⟩
  rcases (layerChildren .branch).certification.hasCorrespondingState
      (structuralState .branch) with ⟨branch, branchCorresponds⟩
  let merged := mergeStoredState (stored .stored) (branch .stored)
  refine ⟨merged, ?_, ?_⟩
  · have equal : storedContractState merged = stored := by
      funext name
      cases name
      simp [storedContractState, merged]
    rw [equal]
    exact storedCorresponds
  · have equal : branchContractState merged = branch := by
      funext name
      cases name
      simp [branchContractState, merged, mergeStoredState]
    rw [equal]
    exact branchCorresponds

private theorem implements :
    Contracts.Cycle.Implements (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have childEvaluation (child : Instance) : ∃ state,
      (childContracts child).EvaluatesTo
        (ProposedValues.childInputs body
          (fun name => (layerChildren name).moduleStructure) inputs proposal.2 child)
        state (proposal.2 child).outputs
        ((childContracts child).stateRule.apply
          (ProposedValues.childInputs body
            (fun name => (layerChildren name).moduleStructure) inputs proposal.2 child)
          state) := by
    rcases (layerChildren child).certification.hasCorrespondingState
        (structuralState child) with ⟨state, stateCorresponds⟩
    exact ⟨state, (childSolutionMatchesContract layerChildren inputs structuralState
      proposal satisfies child state stateCorresponds).1⟩
  have captureEnableEval := (childEvaluation .captureEnable).choose_spec
  have resetEval := (childEvaluation .reset).choose_spec
  have opcodeEval := (childEvaluation .opcode).choose_spec
  have funct3Eval := (childEvaluation .funct3).choose_spec
  have decodedRdEval := (childEvaluation .decodedRd).choose_spec
  have decodedRs1Eval := (childEvaluation .decodedRs1).choose_spec
  have decodedRs2Eval := (childEvaluation .decodedRs2).choose_spec
  have opcodeLuiEval := (childEvaluation .opcodeLui).choose_spec
  have opcodeAuipcEval := (childEvaluation .opcodeAuipc).choose_spec
  have opcodeJalEval := (childEvaluation .opcodeJal).choose_spec
  have opcodeJalrEval := (childEvaluation .opcodeJalr).choose_spec
  have opcodeBranchEval := (childEvaluation .opcodeBranch).choose_spec
  have opcodeLoadEval := (childEvaluation .opcodeLoad).choose_spec
  have opcodeStoreEval := (childEvaluation .opcodeStore).choose_spec
  have opcodeAluImmEval := (childEvaluation .opcodeAluImm).choose_spec
  have opcodeAluRegEval := (childEvaluation .opcodeAluReg).choose_spec
  have funct3ZeroEval := (childEvaluation .funct3Zero).choose_spec
  have jalrEval := (childEvaluation .jalr).choose_spec
  have zeroEval := (childEvaluation .zero).choose_spec
  have immediateEval := (childEvaluation .immediate).choose_spec
  have storedNextEval := (childEvaluation .storedNext).choose_spec
  have storedOutputsEval := (childEvaluation .storedOutputs).choose_spec
  have storedMatch := childSolutionMatchesContract layerChildren inputs structuralState
    proposal satisfies .stored (storedContractState contractState) corresponds.1
  have branchMatch := childSolutionMatchesContract layerChildren inputs structuralState
    proposal satisfies .branch (branchContractState contractState) corresponds.2

  have captureEnableValue : (proposal.2 .captureEnable).outputs .output =
      (inputs .mem_do_rinst && inputs .mem_done) := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      (captureEnableEval.1 Primitives.AndRule.apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, SignalSource.value] using equation
  have resetValue : (proposal.2 .reset).outputs .output = !inputs .resetn := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      (resetEval.1 Primitives.NotRule.apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, SignalSource.value] using equation
  have opcodeValue : (proposal.2 .opcode).outputs .result =
      opcodeBits (inputs .mem_rdata_latched) := by
    have equation := (Modules.VectorSlice.outputRule_holds_iff .bit 0 7 25 _ _ _).mp
      (opcodeEval.1 Modules.VectorSlice.Rule.apply)
    change (proposal.2 .opcode).outputs .result =
      Modules.VectorSlice.slice (prefixWidth := 0) (width := 7) (suffixWidth := 25)
        (inputs .mem_rdata_latched)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, SignalSource.value] using equation
  have funct3Value : (proposal.2 .funct3).outputs .result =
      funct3Bits (inputs .mem_rdata_latched) := by
    have equation := (Modules.VectorSlice.outputRule_holds_iff .bit 12 3 17 _ _ _).mp
      (funct3Eval.1 Modules.VectorSlice.Rule.apply)
    change (proposal.2 .funct3).outputs .result =
      Modules.VectorSlice.slice (prefixWidth := 12) (width := 3) (suffixWidth := 17)
        (inputs .mem_rdata_latched)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, SignalSource.value] using equation
  have decodedRdValue : (proposal.2 .decodedRd).outputs .result =
      addressBits 7 20 (inputs .mem_rdata_latched) := by
    have equation := (Modules.VectorSlice.outputRule_holds_iff .bit 7 5 20 _ _ _).mp
      (decodedRdEval.1 Modules.VectorSlice.Rule.apply)
    change (proposal.2 .decodedRd).outputs .result =
      Modules.VectorSlice.slice (prefixWidth := 7) (width := 5) (suffixWidth := 20)
        (inputs .mem_rdata_latched)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, SignalSource.value] using equation
  have decodedRs1Value : (proposal.2 .decodedRs1).outputs .result =
      addressBits 15 12 (inputs .mem_rdata_latched) := by
    have equation := (Modules.VectorSlice.outputRule_holds_iff .bit 15 5 12 _ _ _).mp
      (decodedRs1Eval.1 Modules.VectorSlice.Rule.apply)
    change (proposal.2 .decodedRs1).outputs .result =
      Modules.VectorSlice.slice (prefixWidth := 15) (width := 5) (suffixWidth := 12)
        (inputs .mem_rdata_latched)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, SignalSource.value] using equation
  have decodedRs2Value : (proposal.2 .decodedRs2).outputs .result =
      addressBits 20 7 (inputs .mem_rdata_latched) := by
    have equation := (Modules.VectorSlice.outputRule_holds_iff .bit 20 5 7 _ _ _).mp
      (decodedRs2Eval.1 Modules.VectorSlice.Rule.apply)
    change (proposal.2 .decodedRs2).outputs .result =
      Modules.VectorSlice.slice (prefixWidth := 20) (width := 5) (suffixWidth := 7)
        (inputs .mem_rdata_latched)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, SignalSource.value] using equation
  have opcodeLuiValue : (proposal.2 .opcodeLui).outputs .result =
      matchesBits 7 0x37 (opcodeBits (inputs .mem_rdata_latched)) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (bits 7 0x37) _ _ _).mp
        (opcodeLuiEval.1 Modules.Equality.Rule.apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.instanceOutput, SignalSource.value, opcodeValue, matchesBits] using equation
  have opcodeAuipcValue : (proposal.2 .opcodeAuipc).outputs .result =
      matchesBits 7 0x17 (opcodeBits (inputs .mem_rdata_latched)) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (bits 7 0x17) _ _ _).mp
        (opcodeAuipcEval.1 Modules.Equality.Rule.apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.instanceOutput, SignalSource.value, opcodeValue, matchesBits] using equation
  have opcodeJalValue : (proposal.2 .opcodeJal).outputs .result =
      matchesBits 7 0x6f (opcodeBits (inputs .mem_rdata_latched)) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (bits 7 0x6f) _ _ _).mp
        (opcodeJalEval.1 Modules.Equality.Rule.apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.instanceOutput, SignalSource.value, opcodeValue, matchesBits] using equation
  have opcodeJalrValue : (proposal.2 .opcodeJalr).outputs .result =
      matchesBits 7 0x67 (opcodeBits (inputs .mem_rdata_latched)) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (bits 7 0x67) _ _ _).mp
        (opcodeJalrEval.1 Modules.Equality.Rule.apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.instanceOutput, SignalSource.value, opcodeValue, matchesBits] using equation
  have opcodeBranchValue : (proposal.2 .opcodeBranch).outputs .result =
      matchesBits 7 0x63 (opcodeBits (inputs .mem_rdata_latched)) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (bits 7 0x63) _ _ _).mp
        (opcodeBranchEval.1 Modules.Equality.Rule.apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.instanceOutput, SignalSource.value, opcodeValue, matchesBits] using equation
  have opcodeLoadValue : (proposal.2 .opcodeLoad).outputs .result =
      matchesBits 7 0x03 (opcodeBits (inputs .mem_rdata_latched)) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (bits 7 0x03) _ _ _).mp
        (opcodeLoadEval.1 Modules.Equality.Rule.apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.instanceOutput, SignalSource.value, opcodeValue, matchesBits] using equation
  have opcodeStoreValue : (proposal.2 .opcodeStore).outputs .result =
      matchesBits 7 0x23 (opcodeBits (inputs .mem_rdata_latched)) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (bits 7 0x23) _ _ _).mp
        (opcodeStoreEval.1 Modules.Equality.Rule.apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.instanceOutput, SignalSource.value, opcodeValue, matchesBits] using equation
  have opcodeAluImmValue : (proposal.2 .opcodeAluImm).outputs .result =
      matchesBits 7 0x13 (opcodeBits (inputs .mem_rdata_latched)) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (bits 7 0x13) _ _ _).mp
        (opcodeAluImmEval.1 Modules.Equality.Rule.apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.instanceOutput, SignalSource.value, opcodeValue, matchesBits] using equation
  have opcodeAluRegValue : (proposal.2 .opcodeAluReg).outputs .result =
      matchesBits 7 0x33 (opcodeBits (inputs .mem_rdata_latched)) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (bits 7 0x33) _ _ _).mp
        (opcodeAluRegEval.1 Modules.Equality.Rule.apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.instanceOutput, SignalSource.value, opcodeValue, matchesBits] using equation
  have funct3ZeroValue : (proposal.2 .funct3Zero).outputs .result =
      matchesBits 3 0 (funct3Bits (inputs .mem_rdata_latched)) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 3 .bit) (bits 3 0) _ _ _).mp
        (funct3ZeroEval.1 Modules.Equality.Rule.apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.instanceOutput, SignalSource.value, funct3Value, matchesBits] using equation
  have jalrValue : (proposal.2 .jalr).outputs .output =
      (matchesBits 7 0x67 (opcodeBits (inputs .mem_rdata_latched)) &&
        matchesBits 3 0 (funct3Bits (inputs .mem_rdata_latched))) := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      (jalrEval.1 Primitives.AndRule.apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.instanceOutput, SignalSource.value, opcodeJalrValue,
      funct3ZeroValue] using equation
  have zeroValue : (proposal.2 .zero).outputs .output = false := by
    exact Modules.Constant.output_of_evaluatesTo .bit false _ _ _ _ zeroEval
  have immediateValue : (proposal.2 .immediate).outputs .output =
      immediateJBits (inputs .mem_rdata_latched) := by
    have equation := Modules.VectorLayout.output_of_evaluatesTo 32 32
      immediateJLayout _ _ _ _ immediateEval
    normalize_child_hyp equation unfolding body, wiring, context
    exact equation

  have storedNextValue : (proposal.2 .storedNext).outputs .value =
      captureData (valuesOf inputs) := by
    have valueEquation := (Modules.NamedTupleCombiner.outputRule_holds_iff
      storedMap _ _ _).mp
      (storedNextEval.1 Modules.NamedTupleAdapterRule.apply)
    normalize_child_hyp valueEquation unfolding body, wiring, context
    rw [valueEquation]
    rw [Modules.NamedTupleCombiner.combinedValue_eq_pack]
    change storedMap.pack _ = storedMap.pack (captureValues (valuesOf inputs))
    apply congrArg storedMap.pack
    funext field
    cases field with
    | instr_lui => exact opcodeLuiValue
    | instr_auipc => exact opcodeAuipcValue
    | instr_jal => exact opcodeJalValue
    | instr_jalr => exact jalrValue
    | decoded_rd => exact decodedRdValue
    | decoded_rs1 => exact decodedRs1Value
    | decoded_rs2 => exact decodedRs2Value
    | decoded_imm_j => exact immediateValue
    | compressed_instr => exact zeroValue
    | is_lb_lh_lw_lbu_lhu => exact opcodeLoadValue
    | is_sb_sh_sw => exact opcodeStoreValue
    | is_alu_reg_imm => exact opcodeAluImmValue
    | is_alu_reg_reg => exact opcodeAluRegValue
  have storedCurrent : (proposal.2 .stored).outputs .q = storedValue contractState := by
    exact (Modules.EnabledRegister.observeRule_holds_iff storedType _ _ _).mp
      (storedMatch.1.1 Modules.EnabledRegister.Rule.observe)
  have storedOutputsValue : (proposal.2 .storedOutputs).outputs =
      Modules.NamedTupleSplitter.splitValue storedMap
        (storedValue contractState) := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      storedMap _ _ _).mp
      (storedOutputsEval.1 Modules.NamedTupleAdapterRule.apply)
    have inputsEqual : ProposedValues.childInputs body
        (fun name => (layerChildren name).moduleStructure) inputs proposal.2 .storedOutputs =
        (fun | .value => storedValue contractState) := by
      funext port
      cases port
      change (proposal.2 .stored).outputs .q = storedValue contractState
      exact storedCurrent
    rw [inputsEqual] at equation
    exact equation
  have branchCurrent : (proposal.2 .branch).outputs .value =
      contractState .is_beq_bne_blt_bge_bltu_bgeu := by
    exact (Modules.EnabledResetRegister.observeRule_holds_iff .bit false _ _ _).mp
      (branchMatch.1.1 Modules.EnabledResetRegister.Rule.observe)

  have storedOutputValue (field : StoredField) :
      (proposal.2 .storedOutputs).outputs field =
        storedMap.unpack (storedValue contractState) field := by
    rw [storedOutputsValue]
    unfold storedValue
    rw [Modules.NamedTupleSplitter.splitValue_pack, storedMap.unpack_pack]
  let nextContractState := nextState (valuesOf inputs) contractState
  refine ⟨nextContractState, ?_, ?_⟩
  · constructor
    · intro rule
      cases rule
      rw [outputRule_holds_iff]
      funext output
      have boundary := satisfies.1 output
      cases output <;>
        simp [body, wiring, context, EndpointContext.instanceOutput,
          SignalSource.value] at boundary ⊢
      all_goals first | exact boundary.trans branchCurrent | exact boundary.trans (storedOutputValue _)
    · rfl
  · constructor
    · have stateEqual : storedContractState nextContractState =
          (Modules.EnabledRegister.stateRule storedType).apply
            (ProposedValues.childInputs body
              (fun name => (layerChildren name).moduleStructure)
              inputs proposal.2 .stored)
            (storedContractState contractState) := by
        funext name
        cases name
        change storedValue (nextState (valuesOf inputs) contractState) =
          bif (proposal.2 .captureEnable).outputs .output
            then (proposal.2 .storedNext).outputs .value
            else storedValue contractState
        rw [captureEnableValue, storedNextValue, storedValue_nextState,
          storedValue_captured]
        cases inputRinst : inputs .mem_do_rinst <;>
          cases inputDone : inputs .mem_done <;>
          simp [valuesOf, inputRinst, inputDone]
      rw [stateEqual]
      exact storedMatch.2
    · have stateEqual : branchContractState nextContractState =
          (Modules.EnabledResetRegister.stateRule .bit false).apply
            (ProposedValues.childInputs body
              (fun name => (layerChildren name).moduleStructure)
              inputs proposal.2 .branch)
            (branchContractState contractState) := by
        funext name
        cases name
        change nextState (valuesOf inputs) contractState
              .is_beq_bne_blt_bge_bltu_bgeu =
          bif (proposal.2 .reset).outputs .output then false
          else bif (proposal.2 .captureEnable).outputs .output
            then (proposal.2 .opcodeBranch).outputs .result
            else contractState .is_beq_bne_blt_bge_bltu_bgeu
        rw [resetValue, captureEnableValue, opcodeBranchValue,
          branch_nextState]
        cases inputResetn : inputs .resetn <;>
          cases inputRinst : inputs .mem_do_rinst <;>
          cases inputDone : inputs .mem_done <;>
          simp [valuesOf, inputResetn, inputRinst, inputDone]
      rw [stateEqual]
      exact branchMatch.2

end Certification

/-! The concrete PicoRV32 decoder capture hierarchy is certified against its
cycle contract while the layer proof remains parametric in child structures. -/
module_cycle_certification certification for moduleStructure via body
    with childContracts implementing cycleContract where
  schedules := derivedRuleSchedules,
  structuralChildren := structuralChildren,
  certifiedChildren := certifiedChildren,
  structuresMatch := certifiedChildren_moduleStructure,
  stateCorresponds := stateCorresponds,
  stateCoverage := hasCorrespondingState,
  implements := implements

end Silean.Examples.PicoRV.Decoder.CaptureStage
