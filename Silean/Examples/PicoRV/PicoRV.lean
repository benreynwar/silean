import Silean.Authoring.ModuleDesign
import Silean.Examples.PicoRV.ControlTheorems
import Silean.Examples.PicoRV.DatapathTheorems
import Silean.Examples.PicoRV.DecoderTheorems
import Silean.Examples.PicoRV.MemoryTheorems
import Silean.Examples.PicoRV.RegsTheorems

namespace Silean.Examples.PicoRV.PicoRV

open Silean
open Silean.Authoring

/-! The configured PicoRV32 top-level hardware boundary. All five direct
children use their certified structural designs. -/

module_ports ports where
  input resetn : .bit,
  input mem_ready : .bit,
  input mem_rdata : .vector 32 .bit,
  output trap : .bit,
  output mem_valid : .bit,
  output mem_instr : .bit,
  output mem_addr : .vector 32 .bit,
  output mem_wdata : .vector 32 .bit,
  output mem_wstrb : .vector 4 .bit,
  output mem_la_read : .bit,
  output mem_la_write : .bit,
  output mem_la_addr : .vector 32 .bit,
  output mem_la_wdata : .vector 32 .bit,
  output mem_la_wstrb : .vector 4 .bit

end Silean.Examples.PicoRV.PicoRV

namespace Silean.Examples.PicoRV

open Silean
open Silean.Authoring

/-! The direct children follow the reviewed source-region split. -/
module_design PicoRV where
  boundary (PicoRV.ports) (naming := PicoRV.Naming.ports)
  instances {
    control := Control.design,
    datapath := Datapath.design,
    mem := Memory.design,
    decoder := Decoder.design,
    cpuregs := Regs.design }
  wiring {
  outputs {
    -- The registered trap output belongs to control.
    .trap := control.trap,
    -- The ordinary and look-ahead memory interfaces belong to `mem`.
    .mem_valid := mem.mem_valid,
    .mem_instr := mem.mem_instr,
    .mem_addr := mem.mem_addr,
    .mem_wdata := mem.mem_wdata,
    .mem_wstrb := mem.mem_wstrb,
    .mem_la_read := mem.mem_la_read,
    .mem_la_write := mem.mem_la_write,
    .mem_la_addr := mem.mem_la_addr,
    .mem_la_wdata := mem.mem_la_wdata,
    .mem_la_wstrb := mem.mem_la_wstrb }
  -- Control observes reset, decoded instruction classes, datapath decisions,
  -- and memory completion.
  instance (.control) {
    .resetn := input.resetn,
    .instr_jal := decoder.instr_jal,
    .instr_jalr := decoder.instr_jalr,
    .instr_lb := decoder.instr_lb,
    .instr_lbu := decoder.instr_lbu,
    .instr_lh := decoder.instr_lh,
    .instr_lhu := decoder.instr_lhu,
    .instr_lw := decoder.instr_lw,
    .instr_sb := decoder.instr_sb,
    .instr_sh := decoder.instr_sh,
    .instr_sw := decoder.instr_sw,
    .instr_trap := decoder.instr_trap,
    .is_lui_auipc_jal := decoder.is_lui_auipc_jal,
    .is_lb_lh_lw_lbu_lhu := decoder.is_lb_lh_lw_lbu_lhu,
    .is_slli_srli_srai := decoder.is_slli_srli_srai,
    .is_jalr_addi_slti_sltiu_xori_ori_andi :=
      decoder.is_jalr_addi_slti_sltiu_xori_ori_andi,
    .is_sb_sh_sw := decoder.is_sb_sh_sw,
    .is_sll_srl_sra := decoder.is_sll_srl_sra,
    .is_beq_bne_blt_bge_bltu_bgeu := decoder.is_beq_bne_blt_bge_bltu_bgeu,
    .is_lbu_lhu_lw := decoder.is_lbu_lhu_lw,
    .decoded_rd := decoder.decoded_rd,
    .reg_pc := datapath.reg_pc,
    .reg_op1 := datapath.reg_op1,
    .reg_sh := datapath.reg_sh,
    .alu_out_0 := datapath.alu_out_0,
    .mem_done := mem.mem_done }

  -- Datapath state advances under registered control, decoded selectors,
  -- register-file reads, and completed memory data.
  instance (.datapath) {
    .resetn := input.resetn,
    .cpu_state := control.cpu_state,
    .latched_store := control.latched_store,
    .latched_stalu := control.latched_stalu,
    .latched_branch := control.latched_branch,
    .latched_is_lu := control.latched_is_lu,
    .latched_is_lh := control.latched_is_lh,
    .latched_is_lb := control.latched_is_lb,
    .mem_do_prefetch := control.mem_do_prefetch,
    .mem_do_rdata := control.mem_do_rdata,
    .mem_do_wdata := control.mem_do_wdata,
    .decoder_trigger := control.decoder_trigger,
    .instr_lui := decoder.instr_lui,
    .instr_jal := decoder.instr_jal,
    .instr_trap := decoder.instr_trap,
    .instr_sub := decoder.instr_sub,
    .instr_beq := decoder.instr_beq,
    .instr_bne := decoder.instr_bne,
    .instr_bge := decoder.instr_bge,
    .instr_bgeu := decoder.instr_bgeu,
    .instr_xori := decoder.instr_xori,
    .instr_xor := decoder.instr_xor,
    .instr_ori := decoder.instr_ori,
    .instr_or := decoder.instr_or,
    .instr_andi := decoder.instr_andi,
    .instr_and := decoder.instr_and,
    .instr_slli := decoder.instr_slli,
    .instr_srli := decoder.instr_srli,
    .instr_srai := decoder.instr_srai,
    .instr_sll := decoder.instr_sll,
    .instr_srl := decoder.instr_srl,
    .instr_sra := decoder.instr_sra,
    .is_lui_auipc_jal := decoder.is_lui_auipc_jal,
    .is_lb_lh_lw_lbu_lhu := decoder.is_lb_lh_lw_lbu_lhu,
    .is_slli_srli_srai := decoder.is_slli_srli_srai,
    .is_jalr_addi_slti_sltiu_xori_ori_andi :=
      decoder.is_jalr_addi_slti_sltiu_xori_ori_andi,
    .is_lui_auipc_jal_jalr_addi_add_sub :=
      decoder.is_lui_auipc_jal_jalr_addi_add_sub,
    .is_slti_blt_slt := decoder.is_slti_blt_slt,
    .is_sltiu_bltu_sltu := decoder.is_sltiu_bltu_sltu,
    .is_compare := decoder.is_compare,
    .decoded_imm := decoder.decoded_imm,
    .decoded_imm_j := decoder.decoded_imm_j,
    .decoded_rs2 := decoder.decoded_rs2,
    .cpuregs_rs1 := cpuregs.cpuregs_rs1,
    .cpuregs_rs2 := cpuregs.cpuregs_rs2,
    .mem_done := mem.mem_done,
    .mem_rdata_word := mem.mem_rdata_word }

  -- Memory receives commands from control, address/data values from the
  -- datapath, and the external ready/read-data interface.
  instance (.mem) {
    .resetn := input.resetn,
    .trap := control.trap,
    .mem_do_prefetch := control.mem_do_prefetch,
    .mem_do_rinst := control.mem_do_rinst,
    .mem_do_rdata := control.mem_do_rdata,
    .mem_do_wdata := control.mem_do_wdata,
    .next_pc := datapath.next_pc,
    .reg_op1 := datapath.reg_op1,
    .reg_op2 := datapath.reg_op2,
    .mem_wordsize := control.mem_wordsize,
    .mem_ready := input.mem_ready,
    .mem_rdata := input.mem_rdata }

  -- Decoder consumes the memory response under control's registered trigger.
  instance (.decoder) {
    .resetn := input.resetn,
    .mem_do_rinst := control.mem_do_rinst,
    .mem_done := mem.mem_done,
    .mem_rdata_latched := mem.mem_rdata_latched,
    .decoder_trigger := control.decoder_trigger,
    .decoder_pseudo_trigger := control.decoder_pseudo_trigger,
    .mem_rdata_q := mem.mem_rdata_q }

  -- The register file reads decoder addresses and writes the datapath result
  -- under control's write enable and registered destination.
  instance (.cpuregs) {
    .resetn := input.resetn,
    .decoded_rs1 := decoder.decoded_rs1,
    .decoded_rs2 := decoder.decoded_rs2,
    .cpuregs_write := control.cpuregs_write,
    .latched_rd := control.latched_rd,
    .cpuregs_wrdata := datapath.cpuregs_wrdata } }

end Silean.Examples.PicoRV
