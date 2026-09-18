import PicoRV.Decoder.DecoderCaptureStage
import Silean.Modules.VectorSlice.VectorSliceTheorems
import Silean.Modules.EqualsConstant.EqualsConstantTheorems
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Modules.EnabledRegister.EnabledRegisterTheorems
import Silean.Modules.EnabledResetRegister.EnabledResetRegisterTheorems
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems
import Silean.Modules.VectorLayout.VectorLayoutTheorems
import Silean.Primitives.Not

/-! Internal schedules, state correspondence, and structural certification for
the registered decoder capture stage. -/

namespace PicoRV.Decoder.CaptureStage

open Silean
open Silean.Authoring
open PicoRV.Decoder
open Silean.Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  captureEnable := Silean.Primitives.andCertified.certification,
  reset := Silean.Primitives.notCertified.certification,
  opcode := Silean.Modules.VectorSlice.certification .bit 0 7 25,
  funct3 := Silean.Modules.VectorSlice.certification .bit 12 3 17,
  decodedRd := Silean.Modules.VectorSlice.certification .bit 7 5 20,
  decodedRs1 := Silean.Modules.VectorSlice.certification .bit 15 5 12,
  decodedRs2 := Silean.Modules.VectorSlice.certification .bit 20 5 7,
  opcodeLui := Silean.Modules.EqualsConstant.certification (.vector 7 .bit) (bits 7 0x37),
  opcodeAuipc := Silean.Modules.EqualsConstant.certification (.vector 7 .bit) (bits 7 0x17),
  opcodeJal := Silean.Modules.EqualsConstant.certification (.vector 7 .bit) (bits 7 0x6f),
  opcodeJalr := Silean.Modules.EqualsConstant.certification (.vector 7 .bit) (bits 7 0x67),
  opcodeBranch := Silean.Modules.EqualsConstant.certification (.vector 7 .bit) (bits 7 0x63),
  opcodeLoad := Silean.Modules.EqualsConstant.certification (.vector 7 .bit) (bits 7 0x03),
  opcodeStore := Silean.Modules.EqualsConstant.certification (.vector 7 .bit) (bits 7 0x23),
  opcodeAluImm := Silean.Modules.EqualsConstant.certification (.vector 7 .bit) (bits 7 0x13),
  opcodeAluReg := Silean.Modules.EqualsConstant.certification (.vector 7 .bit) (bits 7 0x33),
  funct3Zero := Silean.Modules.EqualsConstant.certification (.vector 3 .bit) (bits 3 0),
  jalr := Silean.Primitives.andCertified.certification,
  zero := Silean.Modules.Constant.certification .bit false,
  immediate := Silean.Modules.VectorLayout.certification 32 32 immediateJLayout,
  storedNext := Silean.Modules.NamedTupleCombiner.certification storedMap,
  stored := Silean.Modules.EnabledRegister.certification storedType,
  storedOutputs := Silean.Modules.NamedTupleSplitter.certification storedMap,
  branch := Silean.Modules.EnabledResetRegister.certification .bit false

/-! ## Structural schedules -/

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .outputs => [.stored => Silean.Modules.EnabledRegister.Rule.observe,
      .storedOutputs => Silean.Modules.NamedTupleSplitter.Rule.apply,
      .branch => Silean.Modules.EnabledResetRegister.Rule.observe]
  state := [.captureEnable => Silean.Primitives.AndRule.apply,
    .reset => Silean.Primitives.NotRule.apply,
    {.opcode, .funct3, .decodedRd, .decodedRs1, .decodedRs2} =>
      Silean.Modules.VectorSlice.Rule.apply,
    .zero => Silean.Primitives.ConstantRule.apply,
    {.opcodeLui, .opcodeAuipc, .opcodeJal, .opcodeJalr, .opcodeBranch,
      .opcodeLoad, .opcodeStore, .opcodeAluImm, .opcodeAluReg, .funct3Zero} =>
      Silean.Modules.EqualsConstant.Rule.apply,
    .jalr => Silean.Primitives.AndRule.apply,
    .immediate => Silean.Modules.VectorLayout.Rule.apply,
    .storedNext => Silean.Modules.NamedTupleCombiner.Rule.apply]

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
      Silean.SignalMap.set]

private theorem branch_nextState (inputs : Inputs) (state : stateMap.Values) :
    nextState inputs state .is_beq_bne_blt_bge_bltu_bgeu =
      bif !inputs.resetn then false
      else bif (inputs.mem_do_rinst && inputs.mem_done)
        then matchesBits 7 0x63 (opcodeBits inputs.mem_rdata_latched)
        else state .is_beq_bne_blt_bge_bltu_bgeu := by
  rcases inputs with ⟨resetn, memDoRinst, memDone, word⟩
  cases resetn <;> cases memDoRinst <;> cases memDone <;>
    simp [nextState, captured, Silean.SignalMap.set]

private theorem storedValue_nextState (inputs : Inputs) (state : stateMap.Values) :
    storedValue (nextState inputs state) = storedValue (captured inputs state) := by
  rcases inputs with ⟨resetn, memDoRinst, memDone, word⟩
  cases resetn <;> simp [nextState, storedValue]
  apply congrArg storedMap.pack
  funext field
  cases field <;>
    simp [storedValues, stateMap, Silean.SignalMap.set]

private def storedContractState (state : stateMap.Values) :
    (Silean.Modules.EnabledRegister.cycleContract storedType).state.Values :=
  fun | .stored => storedValue state

private def branchContractState (state : stateMap.Values) :
    (Silean.Modules.EnabledResetRegister.cycleContract .bit false).state.Values :=
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

private def stateCorresponds (contractState : stateMap.Values)
    (structuralState : (Silean.Contracts.Cycle.Certification.Layer.moduleStructure
      body layerChildren).State) : Prop :=
  (layerChildren .stored).certification.stateCorresponds
      (storedContractState contractState) (structuralState .stored) ∧
    (layerChildren .branch).certification.stateCorresponds
      (branchContractState contractState) (structuralState .branch)

private theorem hasCorrespondingState
    (structuralState : (Silean.Contracts.Cycle.Certification.Layer.moduleStructure
      body layerChildren).State) :
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
    Silean.Contracts.Cycle.ImplementsSolutions
      (Silean.Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  have coveredMatch (child : Instance) :=
    (childSolutionMatchesCoveredContract layerChildren hierStep satisfies child).choose_spec
  have storedMatch := childSolutionMatchesContract layerChildren hierStep satisfies
    .stored (storedContractState contractState) corresponds.1
  have branchMatch := childSolutionMatchesContract layerChildren hierStep satisfies
    .branch (branchContractState contractState) corresponds.2

  have captureEnableValue : hierStep.childOutputs .captureEnable .output =
      (hierStep.inputs .mem_do_rinst && hierStep.inputs .mem_done) := by
    have equation := (Silean.Primitives.andOutputRule_holds_iff _ _ _).mp
      ((coveredMatch .captureEnable).ruleHolds Silean.Primitives.AndRule.apply)
    simpa [body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.SignalSource.value] using equation
  have resetValue : hierStep.childOutputs .reset .output = !hierStep.inputs .resetn := by
    have equation := (Silean.Primitives.notOutputRule_holds_iff _ _ _).mp
      ((coveredMatch .reset).ruleHolds Silean.Primitives.NotRule.apply)
    simpa [body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.SignalSource.value] using equation
  have opcodeValue : hierStep.childOutputs .opcode .result =
      opcodeBits (hierStep.inputs .mem_rdata_latched) := by
    have equation := (Silean.Modules.VectorSlice.outputRule_holds_iff .bit 0 7 25 _ _ _).mp
      ((coveredMatch .opcode).ruleHolds Silean.Modules.VectorSlice.Rule.apply)
    change hierStep.childOutputs .opcode .result =
      Silean.Modules.VectorSlice.slice (prefixWidth := 0) (width := 7) (suffixWidth := 25)
        (hierStep.inputs .mem_rdata_latched)
    simpa [body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.SignalSource.value] using equation
  have funct3Value : hierStep.childOutputs .funct3 .result =
      funct3Bits (hierStep.inputs .mem_rdata_latched) := by
    have equation := (Silean.Modules.VectorSlice.outputRule_holds_iff .bit 12 3 17 _ _ _).mp
      ((coveredMatch .funct3).ruleHolds Silean.Modules.VectorSlice.Rule.apply)
    change hierStep.childOutputs .funct3 .result =
      Silean.Modules.VectorSlice.slice (prefixWidth := 12) (width := 3) (suffixWidth := 17)
        (hierStep.inputs .mem_rdata_latched)
    simpa [body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.SignalSource.value] using equation
  have decodedRdValue : hierStep.childOutputs .decodedRd .result =
      addressBits 7 20 (hierStep.inputs .mem_rdata_latched) := by
    have equation := (Silean.Modules.VectorSlice.outputRule_holds_iff .bit 7 5 20 _ _ _).mp
      ((coveredMatch .decodedRd).ruleHolds Silean.Modules.VectorSlice.Rule.apply)
    change hierStep.childOutputs .decodedRd .result =
      Silean.Modules.VectorSlice.slice (prefixWidth := 7) (width := 5) (suffixWidth := 20)
        (hierStep.inputs .mem_rdata_latched)
    simpa [body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.SignalSource.value] using equation
  have decodedRs1Value : hierStep.childOutputs .decodedRs1 .result =
      addressBits 15 12 (hierStep.inputs .mem_rdata_latched) := by
    have equation := (Silean.Modules.VectorSlice.outputRule_holds_iff .bit 15 5 12 _ _ _).mp
      ((coveredMatch .decodedRs1).ruleHolds Silean.Modules.VectorSlice.Rule.apply)
    change hierStep.childOutputs .decodedRs1 .result =
      Silean.Modules.VectorSlice.slice (prefixWidth := 15) (width := 5) (suffixWidth := 12)
        (hierStep.inputs .mem_rdata_latched)
    simpa [body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.SignalSource.value] using equation
  have decodedRs2Value : hierStep.childOutputs .decodedRs2 .result =
      addressBits 20 7 (hierStep.inputs .mem_rdata_latched) := by
    have equation := (Silean.Modules.VectorSlice.outputRule_holds_iff .bit 20 5 7 _ _ _).mp
      ((coveredMatch .decodedRs2).ruleHolds Silean.Modules.VectorSlice.Rule.apply)
    change hierStep.childOutputs .decodedRs2 .result =
      Silean.Modules.VectorSlice.slice (prefixWidth := 20) (width := 5) (suffixWidth := 7)
        (hierStep.inputs .mem_rdata_latched)
    simpa [body, wiring, context,
      Silean.EndpointContext.moduleInput, Silean.SignalSource.value] using equation
  have opcodeLuiValue : hierStep.childOutputs .opcodeLui .result =
      matchesBits 7 0x37 (opcodeBits (hierStep.inputs .mem_rdata_latched)) := by
    have equation := (Silean.Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (bits 7 0x37) _ _ _).mp
        ((coveredMatch .opcodeLui).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg (fun value =>
      (Silean.SignalType.vector 7 .bit).equal value (bits 7 0x37)) opcodeValue)
  have opcodeAuipcValue : hierStep.childOutputs .opcodeAuipc .result =
      matchesBits 7 0x17 (opcodeBits (hierStep.inputs .mem_rdata_latched)) := by
    have equation := (Silean.Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (bits 7 0x17) _ _ _).mp
        ((coveredMatch .opcodeAuipc).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg (fun value =>
      (Silean.SignalType.vector 7 .bit).equal value (bits 7 0x17)) opcodeValue)
  have opcodeJalValue : hierStep.childOutputs .opcodeJal .result =
      matchesBits 7 0x6f (opcodeBits (hierStep.inputs .mem_rdata_latched)) := by
    have equation := (Silean.Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (bits 7 0x6f) _ _ _).mp
        ((coveredMatch .opcodeJal).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg (fun value =>
      (Silean.SignalType.vector 7 .bit).equal value (bits 7 0x6f)) opcodeValue)
  have opcodeJalrValue : hierStep.childOutputs .opcodeJalr .result =
      matchesBits 7 0x67 (opcodeBits (hierStep.inputs .mem_rdata_latched)) := by
    have equation := (Silean.Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (bits 7 0x67) _ _ _).mp
        ((coveredMatch .opcodeJalr).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg (fun value =>
      (Silean.SignalType.vector 7 .bit).equal value (bits 7 0x67)) opcodeValue)
  have opcodeBranchValue : hierStep.childOutputs .opcodeBranch .result =
      matchesBits 7 0x63 (opcodeBits (hierStep.inputs .mem_rdata_latched)) := by
    have equation := (Silean.Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (bits 7 0x63) _ _ _).mp
        ((coveredMatch .opcodeBranch).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg (fun value =>
      (Silean.SignalType.vector 7 .bit).equal value (bits 7 0x63)) opcodeValue)
  have opcodeLoadValue : hierStep.childOutputs .opcodeLoad .result =
      matchesBits 7 0x03 (opcodeBits (hierStep.inputs .mem_rdata_latched)) := by
    have equation := (Silean.Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (bits 7 0x03) _ _ _).mp
        ((coveredMatch .opcodeLoad).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg (fun value =>
      (Silean.SignalType.vector 7 .bit).equal value (bits 7 0x03)) opcodeValue)
  have opcodeStoreValue : hierStep.childOutputs .opcodeStore .result =
      matchesBits 7 0x23 (opcodeBits (hierStep.inputs .mem_rdata_latched)) := by
    have equation := (Silean.Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (bits 7 0x23) _ _ _).mp
        ((coveredMatch .opcodeStore).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg (fun value =>
      (Silean.SignalType.vector 7 .bit).equal value (bits 7 0x23)) opcodeValue)
  have opcodeAluImmValue : hierStep.childOutputs .opcodeAluImm .result =
      matchesBits 7 0x13 (opcodeBits (hierStep.inputs .mem_rdata_latched)) := by
    have equation := (Silean.Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (bits 7 0x13) _ _ _).mp
        ((coveredMatch .opcodeAluImm).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg (fun value =>
      (Silean.SignalType.vector 7 .bit).equal value (bits 7 0x13)) opcodeValue)
  have opcodeAluRegValue : hierStep.childOutputs .opcodeAluReg .result =
      matchesBits 7 0x33 (opcodeBits (hierStep.inputs .mem_rdata_latched)) := by
    have equation := (Silean.Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (bits 7 0x33) _ _ _).mp
        ((coveredMatch .opcodeAluReg).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg (fun value =>
      (Silean.SignalType.vector 7 .bit).equal value (bits 7 0x33)) opcodeValue)
  have funct3ZeroValue : hierStep.childOutputs .funct3Zero .result =
      matchesBits 3 0 (funct3Bits (hierStep.inputs .mem_rdata_latched)) := by
    have equation := (Silean.Modules.EqualsConstant.outputRule_holds_iff
      (.vector 3 .bit) (bits 3 0) _ _ _).mp
        ((coveredMatch .funct3Zero).ruleHolds Silean.Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrArg (fun value =>
      (Silean.SignalType.vector 3 .bit).equal value (bits 3 0)) funct3Value)
  have jalrValue : hierStep.childOutputs .jalr .output =
      (matchesBits 7 0x67 (opcodeBits (hierStep.inputs .mem_rdata_latched)) &&
        matchesBits 3 0 (funct3Bits (hierStep.inputs .mem_rdata_latched))) := by
    have equation := (Silean.Primitives.andOutputRule_holds_iff _ _ _).mp
      ((coveredMatch .jalr).ruleHolds Silean.Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (apply₂_congr Bool.and opcodeJalrValue funct3ZeroValue)
  have zeroValue : hierStep.childOutputs .zero .output = false := by
    exact Silean.Modules.Constant.output_of_allowed .bit false
      (coveredMatch .zero).allowed
  have immediateValue : hierStep.childOutputs .immediate .output =
      immediateJBits (hierStep.inputs .mem_rdata_latched) := by
    have equation := Silean.Modules.VectorLayout.output_of_allowed 32 32
      immediateJLayout (coveredMatch .immediate).allowed
    normalize_child_hyp equation unfolding wiring, context
    exact equation

  have storedNextValue : hierStep.childOutputs .storedNext .value =
      captureData (valuesOf hierStep.inputs) := by
    have valueEquation := (Silean.Modules.NamedTupleCombiner.outputRule_holds_iff
      storedMap _ _ _).mp
      ((coveredMatch .storedNext).ruleHolds Silean.Modules.NamedTupleCombiner.Rule.apply)
    normalize_child_hyp valueEquation
    simp only [wiring, context, Silean.EndpointContext.moduleInput,
      Silean.EndpointContext.instanceOutput] at valueEquation
    refine valueEquation.trans ?_
    rw [Silean.Modules.NamedTupleCombiner.combinedValue_eq_pack]
    change storedMap.pack _ = storedMap.pack (captureValues (valuesOf hierStep.inputs))
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
  have storedCurrent : hierStep.childOutputs .stored .q = storedValue contractState := by
    exact (Silean.Modules.EnabledRegister.observeRule_holds_iff storedType _ _ _).mp
      (storedMatch.ruleHolds Silean.Modules.EnabledRegister.Rule.observe)
  have storedOutputsValue : hierStep.childOutputs .storedOutputs =
      Silean.Modules.NamedTupleSplitter.splitValue storedMap
        (storedValue contractState) := by
    have equation := (Silean.Modules.NamedTupleSplitter.outputRule_holds_iff
      storedMap _ _ _).mp
      ((coveredMatch .storedOutputs).ruleHolds Silean.Modules.NamedTupleSplitter.Rule.apply)
    dsimp only at equation
    have inputsEqual : body.wiring.childInputValues hierStep.inputs
        hierStep.childOutputs .storedOutputs =
        (fun | .value => storedValue contractState) := by
      funext port
      cases port
      change hierStep.childOutputs .stored .q = storedValue contractState
      exact storedCurrent
    rw [inputsEqual] at equation
    exact equation
  have branchCurrent : hierStep.childOutputs .branch .value =
      contractState .is_beq_bne_blt_bge_bltu_bgeu := by
    exact Silean.Modules.EnabledResetRegister.value_of_allowed branchMatch.allowed

  have storedOutputValue (field : StoredField) :
      hierStep.childOutputs .storedOutputs field =
        storedMap.unpack (storedValue contractState) field := by
    rw [storedOutputsValue]
    unfold storedValue
    rw [Silean.Modules.NamedTupleSplitter.splitValue_pack, storedMap.unpack_pack]
  let nextContractState := nextState (valuesOf hierStep.inputs) contractState
  refine ⟨nextContractState, ?_, ?_⟩
  · constructor
    · intro rule
      cases rule
      rw [outputRule_holds_iff]
      funext output
      have boundary := satisfies.1 output
      dsimp only [body, wiring, context,
        Silean.EndpointContext.instanceOutput,
        Silean.SignalSource.value] at boundary
      cases output <;>
        first
        | exact boundary.trans branchCurrent
        | exact boundary.trans (storedOutputValue _)
    · rfl
  · constructor
    · have stateEqual : storedContractState nextContractState =
          (Silean.Modules.EnabledRegister.stateRule storedType).apply
            (body.wiring.childInputValues hierStep.inputs
              hierStep.childOutputs .stored)
            (storedContractState contractState) := by
        funext name
        cases name
        change storedValue (nextState (valuesOf hierStep.inputs) contractState) =
          bif hierStep.childOutputs .captureEnable .output
            then hierStep.childOutputs .storedNext .value
            else storedValue contractState
        rw [captureEnableValue, storedNextValue, storedValue_nextState,
          storedValue_captured]
        cases inputRinst : hierStep.inputs .mem_do_rinst <;>
          cases inputDone : hierStep.inputs .mem_done <;>
          simp [valuesOf, inputRinst, inputDone]
      rw [stateEqual]
      exact storedMatch.nextCorresponds
    · have stateEqual : branchContractState nextContractState =
          (Silean.Modules.EnabledResetRegister.stateRule .bit false).apply
            (body.wiring.childInputValues hierStep.inputs
              hierStep.childOutputs .branch)
            (branchContractState contractState) := by
        funext name
        cases name
        change nextState (valuesOf hierStep.inputs) contractState
              .is_beq_bne_blt_bge_bltu_bgeu =
          bif hierStep.childOutputs .reset .output then false
          else bif hierStep.childOutputs .captureEnable .output
            then hierStep.childOutputs .opcodeBranch .result
            else contractState .is_beq_bne_blt_bge_bltu_bgeu
        rw [resetValue, captureEnableValue, opcodeBranchValue,
          branch_nextState]
        cases inputResetn : hierStep.inputs .resetn <;>
          cases inputRinst : hierStep.inputs .mem_do_rinst <;>
          cases inputDone : hierStep.inputs .mem_done <;>
          simp [valuesOf, inputResetn, inputRinst, inputDone]
      rw [stateEqual]
      exact branchMatch.nextCorresponds

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

end PicoRV.Decoder.CaptureStage
