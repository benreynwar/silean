import PicoRV.DecoderContract
import PicoRV.Decoder.DecoderCaptureStage
import PicoRV.Decoder.Internal.DecoderResolveStageStructure
import Silean.Authoring.ModuleDesign

namespace PicoRV

open Silean
open Silean.Authoring

/-! Expanded typed connection map for the decoder's two registered stages. -/

module_design Decoder where
  boundary (Decoder.ports) (naming := Decoder.Naming.ports)
  instances {
    capture := Decoder.CaptureStage.design,
    resolve := Decoder.ResolveStage.design }
  wiring {
  outputs {
    .instr_trap := resolve.instr_trap,
    .instr_lui := capture.instr_lui,
    .instr_jal := capture.instr_jal,
    .instr_jalr := capture.instr_jalr,
    .instr_beq := resolve.instr_beq,
    .instr_bne := resolve.instr_bne,
    .instr_bge := resolve.instr_bge,
    .instr_bgeu := resolve.instr_bgeu,
    .instr_lb := resolve.instr_lb,
    .instr_lh := resolve.instr_lh,
    .instr_lw := resolve.instr_lw,
    .instr_lbu := resolve.instr_lbu,
    .instr_lhu := resolve.instr_lhu,
    .instr_sb := resolve.instr_sb,
    .instr_sh := resolve.instr_sh,
    .instr_sw := resolve.instr_sw,
    .instr_xori := resolve.instr_xori,
    .instr_ori := resolve.instr_ori,
    .instr_andi := resolve.instr_andi,
    .instr_slli := resolve.instr_slli,
    .instr_srli := resolve.instr_srli,
    .instr_srai := resolve.instr_srai,
    .instr_sub := resolve.instr_sub,
    .instr_sll := resolve.instr_sll,
    .instr_xor := resolve.instr_xor,
    .instr_srl := resolve.instr_srl,
    .instr_sra := resolve.instr_sra,
    .instr_or := resolve.instr_or,
    .instr_and := resolve.instr_and,
    .decoded_rd := capture.decoded_rd,
    .decoded_rs1 := capture.decoded_rs1,
    .decoded_rs2 := capture.decoded_rs2,
    .decoded_imm := resolve.decoded_imm,
    .decoded_imm_j := capture.decoded_imm_j,
    .is_lui_auipc_jal := resolve.is_lui_auipc_jal,
    .is_lb_lh_lw_lbu_lhu := capture.is_lb_lh_lw_lbu_lhu,
    .is_slli_srli_srai := resolve.is_slli_srli_srai,
    .is_jalr_addi_slti_sltiu_xori_ori_andi :=
      resolve.is_jalr_addi_slti_sltiu_xori_ori_andi,
    .is_sb_sh_sw := capture.is_sb_sh_sw,
    .is_sll_srl_sra := resolve.is_sll_srl_sra,
    .is_lui_auipc_jal_jalr_addi_add_sub :=
      resolve.is_lui_auipc_jal_jalr_addi_add_sub,
    .is_slti_blt_slt := resolve.is_slti_blt_slt,
    .is_sltiu_bltu_sltu := resolve.is_sltiu_bltu_sltu,
    .is_beq_bne_blt_bge_bltu_bgeu := capture.is_beq_bne_blt_bge_bltu_bgeu,
    .is_lbu_lhu_lw := resolve.is_lbu_lhu_lw,
    .is_compare := resolve.is_compare }
  instance (.capture) {
    .resetn := input.resetn,
    .mem_do_rinst := input.mem_do_rinst,
    .mem_done := input.mem_done,
    .mem_rdata_latched := input.mem_rdata_latched }
  instance (.resolve) {
    .resetn := input.resetn,
    .decoder_trigger := input.decoder_trigger,
    .decoder_pseudo_trigger := input.decoder_pseudo_trigger,
    .mem_rdata_q := input.mem_rdata_q,
    .instr_lui := capture.instr_lui,
    .instr_auipc := capture.instr_auipc,
    .instr_jal := capture.instr_jal,
    .instr_jalr := capture.instr_jalr,
    .decoded_imm_j := capture.decoded_imm_j,
    .is_beq_bne_blt_bge_bltu_bgeu := capture.is_beq_bne_blt_bge_bltu_bgeu,
    .is_lb_lh_lw_lbu_lhu := capture.is_lb_lh_lw_lbu_lhu,
    .is_sb_sh_sw := capture.is_sb_sh_sw,
    .is_alu_reg_imm := capture.is_alu_reg_imm,
    .is_alu_reg_reg := capture.is_alu_reg_reg }
  }

end PicoRV
