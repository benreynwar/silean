import PicoRV.Decoder.DecoderTypes
import PicoRV.Decoder.DecoderInstructionMatch
import PicoRV.Decoder.DecoderImmediate
import PicoRV.Decoder.DecoderInstructionSummary
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Contracts.Cycle.CycleContract
import Silean.Contracts.Cycle.CycleEvaluation

namespace PicoRV.Decoder.ResolveStage

open Silean
open Silean.Authoring
open PicoRV.Decoder

/-! The second registered decoder stage. It resolves broad capture-stage
classes into exact instructions, constructs the non-J immediate, and maintains
the registered summary flags with the source's pre-edge timing and priorities. -/

module_ports ports where
  input resetn : .bit,
  input decoder_trigger : .bit,
  input decoder_pseudo_trigger : .bit,
  input mem_rdata_q : .vector 32 .bit,
  input instr_lui : .bit,
  input instr_auipc : .bit,
  input instr_jal : .bit,
  input instr_jalr : .bit,
  input decoded_imm_j : .vector 32 .bit,
  input is_beq_bne_blt_bge_bltu_bgeu : .bit,
  input is_lb_lh_lw_lbu_lhu : .bit,
  input is_sb_sh_sw : .bit,
  input is_alu_reg_imm : .bit,
  input is_alu_reg_reg : .bit,
  output instr_trap : .bit,
  output instr_beq : .bit,
  output instr_bne : .bit,
  output instr_blt : .bit,
  output instr_bge : .bit,
  output instr_bltu : .bit,
  output instr_bgeu : .bit,
  output instr_lb : .bit,
  output instr_lh : .bit,
  output instr_lw : .bit,
  output instr_lbu : .bit,
  output instr_lhu : .bit,
  output instr_sb : .bit,
  output instr_sh : .bit,
  output instr_sw : .bit,
  output instr_addi : .bit,
  output instr_slti : .bit,
  output instr_sltiu : .bit,
  output instr_xori : .bit,
  output instr_ori : .bit,
  output instr_andi : .bit,
  output instr_slli : .bit,
  output instr_srli : .bit,
  output instr_srai : .bit,
  output instr_add : .bit,
  output instr_sub : .bit,
  output instr_sll : .bit,
  output instr_slt : .bit,
  output instr_sltu : .bit,
  output instr_xor : .bit,
  output instr_srl : .bit,
  output instr_sra : .bit,
  output instr_or : .bit,
  output instr_and : .bit,
  output instr_fence : .bit,
  output decoded_imm : .vector 32 .bit,
  output is_lui_auipc_jal : .bit,
  output is_slli_srli_srai : .bit,
  output is_jalr_addi_slti_sltiu_xori_ori_andi : .bit,
  output is_sll_srl_sra : .bit,
  output is_lui_auipc_jal_jalr_addi_add_sub : .bit,
  output is_slti_blt_slt : .bit,
  output is_sltiu_bltu_sltu : .bit,
  output is_lbu_lhu_lw : .bit,
  output is_compare : .bit

inductive Register
  | instr_beq | instr_bne | instr_blt | instr_bge | instr_bltu | instr_bgeu
  | instr_lb | instr_lh | instr_lw | instr_lbu | instr_lhu
  | instr_sb | instr_sh | instr_sw
  | instr_addi | instr_slti | instr_sltiu | instr_xori | instr_ori | instr_andi
  | instr_slli | instr_srli | instr_srai
  | instr_add | instr_sub | instr_sll | instr_slt | instr_sltu
  | instr_xor | instr_srl | instr_sra | instr_or | instr_and
  | instr_ecall_ebreak | instr_fence
  | decoded_imm
  | is_lui_auipc_jal
  | is_slli_srli_srai
  | is_jalr_addi_slti_sltiu_xori_ori_andi
  | is_sll_srl_sra
  | is_lui_auipc_jal_jalr_addi_add_sub
  | is_slti_blt_slt
  | is_sltiu_bltu_sltu
  | is_lbu_lhu_lw
  | is_compare
deriving Enumeration

def registerType : Register → SignalType
  | .decoded_imm => .vector 32 .bit
  | _ => .bit

@[reducible] def stateMap : SignalMap := Silean.EnumeratedMap.of Register registerType

structure Inputs where
  resetn : Bool
  decoder_trigger : Bool
  decoder_pseudo_trigger : Bool
  mem_rdata_q : Word
  instr_lui : Bool
  instr_auipc : Bool
  instr_jal : Bool
  instr_jalr : Bool
  decoded_imm_j : Word
  is_beq_bne_blt_bge_bltu_bgeu : Bool
  is_lb_lh_lw_lbu_lhu : Bool
  is_sb_sh_sw : Bool
  is_alu_reg_imm : Bool
  is_alu_reg_reg : Bool

def valuesOf (inputs : inputMap.Values) : Inputs where
  resetn := inputs .resetn
  decoder_trigger := inputs .decoder_trigger
  decoder_pseudo_trigger := inputs .decoder_pseudo_trigger
  mem_rdata_q := inputs .mem_rdata_q
  instr_lui := inputs .instr_lui
  instr_auipc := inputs .instr_auipc
  instr_jal := inputs .instr_jal
  instr_jalr := inputs .instr_jalr
  decoded_imm_j := inputs .decoded_imm_j
  is_beq_bne_blt_bge_bltu_bgeu := inputs .is_beq_bne_blt_bge_bltu_bgeu
  is_lb_lh_lw_lbu_lhu := inputs .is_lb_lh_lw_lbu_lhu
  is_sb_sh_sw := inputs .is_sb_sh_sw
  is_alu_reg_imm := inputs .is_alu_reg_imm
  is_alu_reg_reg := inputs .is_alu_reg_reg

def matchInputs (inputs : Inputs) : InstructionMatch.Inputs where
  word := inputs.mem_rdata_q
  instr_jalr := inputs.instr_jalr
  is_beq_bne_blt_bge_bltu_bgeu := inputs.is_beq_bne_blt_bge_bltu_bgeu
  is_lb_lh_lw_lbu_lhu := inputs.is_lb_lh_lw_lbu_lhu
  is_sb_sh_sw := inputs.is_sb_sh_sw
  is_alu_reg_imm := inputs.is_alu_reg_imm
  is_alu_reg_reg := inputs.is_alu_reg_reg

def immediateInputs (inputs : Inputs) : Immediate.Inputs where
  word := inputs.mem_rdata_q
  decoded_imm_j := inputs.decoded_imm_j
  instr_jal := inputs.instr_jal
  instr_lui := inputs.instr_lui
  instr_auipc := inputs.instr_auipc
  instr_jalr := inputs.instr_jalr
  is_lb_lh_lw_lbu_lhu := inputs.is_lb_lh_lw_lbu_lhu
  is_alu_reg_imm := inputs.is_alu_reg_imm
  is_beq_bne_blt_bge_bltu_bgeu := inputs.is_beq_bne_blt_bge_bltu_bgeu
  is_sb_sh_sw := inputs.is_sb_sh_sw

def summaryInputs (inputs : Inputs) (state : stateMap.Values) :
    InstructionSummary.Inputs where
  instr_lui := inputs.instr_lui
  instr_auipc := inputs.instr_auipc
  instr_jal := inputs.instr_jal
  instr_jalr := inputs.instr_jalr
  is_beq_bne_blt_bge_bltu_bgeu := inputs.is_beq_bne_blt_bge_bltu_bgeu
  matched
    | .instr_beq => state .instr_beq | .instr_bne => state .instr_bne
    | .instr_blt => state .instr_blt | .instr_bge => state .instr_bge
    | .instr_bltu => state .instr_bltu | .instr_bgeu => state .instr_bgeu
    | .instr_lb => state .instr_lb | .instr_lh => state .instr_lh
    | .instr_lw => state .instr_lw | .instr_lbu => state .instr_lbu
    | .instr_lhu => state .instr_lhu
    | .instr_sb => state .instr_sb | .instr_sh => state .instr_sh
    | .instr_sw => state .instr_sw
    | .instr_addi => state .instr_addi | .instr_slti => state .instr_slti
    | .instr_sltiu => state .instr_sltiu | .instr_xori => state .instr_xori
    | .instr_ori => state .instr_ori | .instr_andi => state .instr_andi
    | .instr_slli => state .instr_slli | .instr_srli => state .instr_srli
    | .instr_srai => state .instr_srai
    | .instr_add => state .instr_add | .instr_sub => state .instr_sub
    | .instr_sll => state .instr_sll | .instr_slt => state .instr_slt
    | .instr_sltu => state .instr_sltu | .instr_xor => state .instr_xor
    | .instr_srl => state .instr_srl | .instr_sra => state .instr_sra
    | .instr_or => state .instr_or | .instr_and => state .instr_and
    | .instr_ecall_ebreak => state .instr_ecall_ebreak
    | .instr_fence => state .instr_fence
    | .is_slli_srli_srai | .is_jalr_addi_slti_sltiu_xori_ori_andi
    | .is_sll_srl_sra => false

def summarized (inputs : Inputs) (state : stateMap.Values) : stateMap.Values
  | .is_lui_auipc_jal =>
      InstructionSummary.outputValues (summaryInputs inputs state) .is_lui_auipc_jal
  | .is_lui_auipc_jal_jalr_addi_add_sub =>
      InstructionSummary.outputValues (summaryInputs inputs state)
        .is_lui_auipc_jal_jalr_addi_add_sub
  | .is_slti_blt_slt =>
      InstructionSummary.outputValues (summaryInputs inputs state) .is_slti_blt_slt
  | .is_sltiu_bltu_sltu =>
      InstructionSummary.outputValues (summaryInputs inputs state) .is_sltiu_bltu_sltu
  | .is_lbu_lhu_lw =>
      InstructionSummary.outputValues (summaryInputs inputs state) .is_lbu_lhu_lw
  | .is_compare =>
      InstructionSummary.outputValues (summaryInputs inputs state) .is_compare
  | register => state register

def decoded (inputs : Inputs) (current updated : stateMap.Values) : stateMap.Values :=
  if !(inputs.decoder_trigger && !inputs.decoder_pseudo_trigger) then updated else
  fun
  | .instr_beq => InstructionMatch.outputValues (matchInputs inputs) .instr_beq
  | .instr_bne => InstructionMatch.outputValues (matchInputs inputs) .instr_bne
  | .instr_blt => InstructionMatch.outputValues (matchInputs inputs) .instr_blt
  | .instr_bge => InstructionMatch.outputValues (matchInputs inputs) .instr_bge
  | .instr_bltu => InstructionMatch.outputValues (matchInputs inputs) .instr_bltu
  | .instr_bgeu => InstructionMatch.outputValues (matchInputs inputs) .instr_bgeu
  | .instr_lb => InstructionMatch.outputValues (matchInputs inputs) .instr_lb
  | .instr_lh => InstructionMatch.outputValues (matchInputs inputs) .instr_lh
  | .instr_lw => InstructionMatch.outputValues (matchInputs inputs) .instr_lw
  | .instr_lbu => InstructionMatch.outputValues (matchInputs inputs) .instr_lbu
  | .instr_lhu => InstructionMatch.outputValues (matchInputs inputs) .instr_lhu
  | .instr_sb => InstructionMatch.outputValues (matchInputs inputs) .instr_sb
  | .instr_sh => InstructionMatch.outputValues (matchInputs inputs) .instr_sh
  | .instr_sw => InstructionMatch.outputValues (matchInputs inputs) .instr_sw
  | .instr_addi => InstructionMatch.outputValues (matchInputs inputs) .instr_addi
  | .instr_slti => InstructionMatch.outputValues (matchInputs inputs) .instr_slti
  | .instr_sltiu => InstructionMatch.outputValues (matchInputs inputs) .instr_sltiu
  | .instr_xori => InstructionMatch.outputValues (matchInputs inputs) .instr_xori
  | .instr_ori => InstructionMatch.outputValues (matchInputs inputs) .instr_ori
  | .instr_andi => InstructionMatch.outputValues (matchInputs inputs) .instr_andi
  | .instr_slli => InstructionMatch.outputValues (matchInputs inputs) .instr_slli
  | .instr_srli => InstructionMatch.outputValues (matchInputs inputs) .instr_srli
  | .instr_srai => InstructionMatch.outputValues (matchInputs inputs) .instr_srai
  | .instr_add => InstructionMatch.outputValues (matchInputs inputs) .instr_add
  | .instr_sub => InstructionMatch.outputValues (matchInputs inputs) .instr_sub
  | .instr_sll => InstructionMatch.outputValues (matchInputs inputs) .instr_sll
  | .instr_slt => InstructionMatch.outputValues (matchInputs inputs) .instr_slt
  | .instr_sltu => InstructionMatch.outputValues (matchInputs inputs) .instr_sltu
  | .instr_xor => InstructionMatch.outputValues (matchInputs inputs) .instr_xor
  | .instr_srl => InstructionMatch.outputValues (matchInputs inputs) .instr_srl
  | .instr_sra => InstructionMatch.outputValues (matchInputs inputs) .instr_sra
  | .instr_or => InstructionMatch.outputValues (matchInputs inputs) .instr_or
  | .instr_and => InstructionMatch.outputValues (matchInputs inputs) .instr_and
  | .instr_ecall_ebreak =>
      InstructionMatch.outputValues (matchInputs inputs) .instr_ecall_ebreak
  | .instr_fence => InstructionMatch.outputValues (matchInputs inputs) .instr_fence
  | .is_slli_srli_srai =>
      InstructionMatch.outputValues (matchInputs inputs) .is_slli_srli_srai
  | .is_jalr_addi_slti_sltiu_xori_ori_andi =>
      InstructionMatch.outputValues (matchInputs inputs)
        .is_jalr_addi_slti_sltiu_xori_ori_andi
  | .is_sll_srl_sra =>
      InstructionMatch.outputValues (matchInputs inputs) .is_sll_srl_sra
  | .is_lui_auipc_jal_jalr_addi_add_sub | .is_compare => false
  | .decoded_imm =>
      (Immediate.evaluate (immediateInputs inputs)).getD (current .decoded_imm)
  | register => updated register

def resetApplied (resetn : Bool) (state : stateMap.Values) : stateMap.Values :=
  if resetn then state else fun
  | .instr_beq | .instr_bne | .instr_blt | .instr_bge | .instr_bltu
  | .instr_bgeu | .instr_addi | .instr_slti | .instr_sltiu | .instr_xori
  | .instr_ori | .instr_andi | .instr_add | .instr_sub | .instr_sll
  | .instr_slt | .instr_sltu | .instr_xor | .instr_srl | .instr_sra
  | .instr_or | .instr_and | .instr_fence | .is_compare => false
  | register => state register

def nextState (inputs : Inputs) (state : stateMap.Values) : stateMap.Values :=
  resetApplied inputs.resetn (decoded inputs state (summarized inputs state))

def recognized (inputs : Inputs) (state : stateMap.Values) : Bool := boolOr [
  inputs.instr_lui, inputs.instr_auipc, inputs.instr_jal, inputs.instr_jalr,
  state .instr_beq, state .instr_bne, state .instr_blt, state .instr_bge,
  state .instr_bltu, state .instr_bgeu, state .instr_lb, state .instr_lh,
  state .instr_lw, state .instr_lbu, state .instr_lhu, state .instr_sb,
  state .instr_sh, state .instr_sw, state .instr_addi, state .instr_slti,
  state .instr_sltiu, state .instr_xori, state .instr_ori, state .instr_andi,
  state .instr_slli, state .instr_srli, state .instr_srai, state .instr_add,
  state .instr_sub, state .instr_sll, state .instr_slt, state .instr_sltu,
  state .instr_xor, state .instr_srl, state .instr_sra, state .instr_or,
  state .instr_and, state .instr_fence]

def outputValues (inputs : Inputs) (state : stateMap.Values) : outputMap.Values
  | .instr_trap => !(recognized inputs state)
  | .instr_beq => state .instr_beq | .instr_bne => state .instr_bne
  | .instr_blt => state .instr_blt | .instr_bge => state .instr_bge
  | .instr_bltu => state .instr_bltu | .instr_bgeu => state .instr_bgeu
  | .instr_lb => state .instr_lb | .instr_lh => state .instr_lh
  | .instr_lw => state .instr_lw | .instr_lbu => state .instr_lbu
  | .instr_lhu => state .instr_lhu
  | .instr_sb => state .instr_sb | .instr_sh => state .instr_sh
  | .instr_sw => state .instr_sw
  | .instr_addi => state .instr_addi | .instr_slti => state .instr_slti
  | .instr_sltiu => state .instr_sltiu | .instr_xori => state .instr_xori
  | .instr_ori => state .instr_ori | .instr_andi => state .instr_andi
  | .instr_slli => state .instr_slli | .instr_srli => state .instr_srli
  | .instr_srai => state .instr_srai
  | .instr_add => state .instr_add | .instr_sub => state .instr_sub
  | .instr_sll => state .instr_sll | .instr_slt => state .instr_slt
  | .instr_sltu => state .instr_sltu | .instr_xor => state .instr_xor
  | .instr_srl => state .instr_srl | .instr_sra => state .instr_sra
  | .instr_or => state .instr_or | .instr_and => state .instr_and
  | .instr_fence => state .instr_fence
  | .decoded_imm => state .decoded_imm
  | .is_lui_auipc_jal => state .is_lui_auipc_jal
  | .is_slli_srli_srai => state .is_slli_srli_srai
  | .is_jalr_addi_slti_sltiu_xori_ori_andi =>
      state .is_jalr_addi_slti_sltiu_xori_ori_andi
  | .is_sll_srl_sra => state .is_sll_srl_sra
  | .is_lui_auipc_jal_jalr_addi_add_sub =>
      state .is_lui_auipc_jal_jalr_addi_add_sub
  | .is_slti_blt_slt => state .is_slti_blt_slt
  | .is_sltiu_bltu_sltu => state .is_sltiu_bltu_sltu
  | .is_lbu_lhu_lw => state .is_lbu_lhu_lw
  | .is_compare => state .is_compare

namespace OutputRule
inductive Input | instr_lui | instr_auipc | instr_jal | instr_jalr
deriving Enumeration
end OutputRule

@[reducible] private def outputInputsGroup : SignalGroup inputMap :=
  Silean.SignalGroup.fromLabels inputMap OutputRule.Input fun
    | .instr_lui => .instr_lui
    | .instr_auipc => .instr_auipc
    | .instr_jal => .instr_jal
    | .instr_jalr => .instr_jalr

def outputInputs (instr_lui instr_auipc instr_jal instr_jalr : Bool) : Inputs :=
  { resetn := true
    decoder_trigger := false
    decoder_pseudo_trigger := false
    mem_rdata_q := wordOfNat 0
    instr_lui, instr_auipc, instr_jal, instr_jalr
    decoded_imm_j := wordOfNat 0
    is_beq_bne_blt_bge_bltu_bgeu := false
    is_lb_lh_lw_lbu_lhu := false
    is_sb_sh_sw := false
    is_alu_reg_imm := false
    is_alu_reg_reg := false }

theorem outputValues_depends_only_on_instruction_flags
    (inputs : Inputs) (state : stateMap.Values) :
    outputValues (outputInputs inputs.instr_lui inputs.instr_auipc
      inputs.instr_jal inputs.instr_jalr) state = outputValues inputs state := by
  funext output
  cases output <;> rfl

def outputRule : Silean.Contracts.Cycle.CycleOutputRule ports stateMap where
  readsInputs := outputInputsGroup
  writesOutputs := .all outputMap
  target inputs state := outputValues
    (outputInputs (inputs .instr_lui) (inputs .instr_auipc)
      (inputs .instr_jal) (inputs .instr_jalr)) state

def stateRule : Silean.Contracts.Cycle.CycleStateRule ports stateMap where
  readsInputs := .all inputMap
  target inputs state := nextState (valuesOf inputs) state

@[simp] theorem outputRule_reads (input : Input) :
    input ∈ outputRule.readsInputs.labels ↔
      input = .instr_lui ∨ input = .instr_auipc ∨ input = .instr_jal ∨
        input = .instr_jalr := by
  change input ∈ outputInputsGroup.labels ↔ _
  letI : DecidableEq Input := inputMap.labels.decidableEq
  cases input <;> decide

@[simp] theorem outputRule_writes (output : Output) :
    output ∈ outputRule.writesOutputs.labels := by
  change output ∈ (Silean.SignalGroup.all outputMap).labels
  rw [Silean.SignalGroup.all_labels]
  exact (outputMap.labels.locate output).mem

@[simp] theorem stateRule_reads (input : Input) :
    input ∈ stateRule.readsInputs.labels := by
  change input ∈ (Silean.SignalGroup.all inputMap).labels
  rw [Silean.SignalGroup.all_labels]
  exact (inputMap.labels.locate input).mem

module_cycle_contract cycleContract for ports where
  state := stateMap
  output_rule outputs := outputRule
  state_rule := stateRule

@[simp] theorem outputRule_holds_iff
    (inputs : ports.inputs.Values) (state : stateMap.Values)
    (outputs : ports.outputs.Values) :
    outputRule.Holds inputs state outputs ↔ outputs = outputValues (valuesOf inputs) state := by
  simp only [outputRule, Silean.Contracts.Cycle.CycleOutputRule.Holds,
    Silean.SignalGroup.all_matches]
  change outputs = outputValues
      (outputInputs (valuesOf inputs).instr_lui (valuesOf inputs).instr_auipc
        (valuesOf inputs).instr_jal (valuesOf inputs).instr_jalr) state ↔ _
  rw [outputValues_depends_only_on_instruction_flags (valuesOf inputs) state]

end PicoRV.Decoder.ResolveStage
