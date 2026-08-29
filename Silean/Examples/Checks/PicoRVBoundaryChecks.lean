import Silean.Examples.PicoRV.Control
import Silean.Examples.PicoRV.Datapath
import Silean.Examples.PicoRV.Decoder
import Silean.Examples.PicoRV.Memory
import Silean.Examples.PicoRV.Regs

namespace Silean.Examples.Checks.PicoRVBoundary

open Silean

namespace P
namespace Control
abbrev Input := Silean.Examples.PicoRV.Control.Input
abbrev Output := Silean.Examples.PicoRV.Control.Output
abbrev inputMap := Silean.Examples.PicoRV.Control.inputMap
abbrev outputMap := Silean.Examples.PicoRV.Control.outputMap
end Control
namespace Datapath
abbrev Input := Silean.Examples.PicoRV.Datapath.Input
abbrev Output := Silean.Examples.PicoRV.Datapath.Output
abbrev inputMap := Silean.Examples.PicoRV.Datapath.inputMap
abbrev outputMap := Silean.Examples.PicoRV.Datapath.outputMap
end Datapath
namespace Decoder
abbrev Input := Silean.Examples.PicoRV.Decoder.Input
abbrev Output := Silean.Examples.PicoRV.Decoder.Output
abbrev inputMap := Silean.Examples.PicoRV.Decoder.inputMap
abbrev outputMap := Silean.Examples.PicoRV.Decoder.outputMap
end Decoder
namespace Memory
abbrev Input := Silean.Examples.PicoRV.Memory.Input
abbrev Output := Silean.Examples.PicoRV.Memory.Output
abbrev inputMap := Silean.Examples.PicoRV.Memory.inputMap
abbrev outputMap := Silean.Examples.PicoRV.Memory.outputMap
end Memory
namespace Regs
abbrev Input := Silean.Examples.PicoRV.Regs.Input
abbrev Output := Silean.Examples.PicoRV.Regs.Output
abbrev inputMap := Silean.Examples.PicoRV.Regs.inputMap
abbrev outputMap := Silean.Examples.PicoRV.Regs.outputMap
end Regs
end P

/-! A compile-time audit of the configured PicoRV32 child boundary. Each child
input names its unique producer below; the four external sources are the only
exceptions. The equalities at the end ensure every listed connection has the
same signal type at both ends. This deliberately does not construct a top-level
`ModuleStructure`. -/

inductive SourcePort
  | resetn | mem_ready | mem_rdata
  | control (port : P.Control.Output)
  | datapath (port : P.Datapath.Output)
  | decoder (port : P.Decoder.Output)
  | memory (port : P.Memory.Output)
  | regs (port : P.Regs.Output)

def sourceType : SourcePort → SignalType
  | .resetn | .mem_ready => .bit
  | .mem_rdata => .vector 32 .bit
  | .control port => P.Control.outputMap.signalType port
  | .datapath port => P.Datapath.outputMap.signalType port
  | .decoder port => P.Decoder.outputMap.signalType port
  | .memory port => P.Memory.outputMap.signalType port
  | .regs port => P.Regs.outputMap.signalType port

def controlSource : P.Control.Input → SourcePort
  | .resetn => .resetn
  | .instr_jal => .decoder .instr_jal
  | .instr_jalr => .decoder .instr_jalr
  | .instr_lb => .decoder .instr_lb
  | .instr_lbu => .decoder .instr_lbu
  | .instr_lh => .decoder .instr_lh
  | .instr_lhu => .decoder .instr_lhu
  | .instr_lw => .decoder .instr_lw
  | .instr_sb => .decoder .instr_sb
  | .instr_sh => .decoder .instr_sh
  | .instr_sw => .decoder .instr_sw
  | .instr_trap => .decoder .instr_trap
  | .is_lui_auipc_jal => .decoder .is_lui_auipc_jal
  | .is_lb_lh_lw_lbu_lhu => .decoder .is_lb_lh_lw_lbu_lhu
  | .is_slli_srli_srai => .decoder .is_slli_srli_srai
  | .is_jalr_addi_slti_sltiu_xori_ori_andi =>
      .decoder .is_jalr_addi_slti_sltiu_xori_ori_andi
  | .is_sb_sh_sw => .decoder .is_sb_sh_sw
  | .is_sll_srl_sra => .decoder .is_sll_srl_sra
  | .is_beq_bne_blt_bge_bltu_bgeu => .decoder .is_beq_bne_blt_bge_bltu_bgeu
  | .is_lbu_lhu_lw => .decoder .is_lbu_lhu_lw
  | .decoded_rd => .decoder .decoded_rd
  | .reg_pc => .datapath .reg_pc
  | .reg_op1 => .datapath .reg_op1
  | .reg_sh => .datapath .reg_sh
  | .alu_out_0 => .datapath .alu_out_0
  | .mem_done => .memory .mem_done

def datapathSource : P.Datapath.Input → SourcePort
  | .resetn => .resetn
  | .cpu_state => .control .cpu_state
  | .latched_store => .control .latched_store
  | .latched_stalu => .control .latched_stalu
  | .latched_branch => .control .latched_branch
  | .latched_is_lu => .control .latched_is_lu
  | .latched_is_lh => .control .latched_is_lh
  | .latched_is_lb => .control .latched_is_lb
  | .mem_do_prefetch => .control .mem_do_prefetch
  | .mem_do_rdata => .control .mem_do_rdata
  | .mem_do_wdata => .control .mem_do_wdata
  | .decoder_trigger => .control .decoder_trigger
  | .instr_lui => .decoder .instr_lui
  | .instr_jal => .decoder .instr_jal
  | .instr_sub => .decoder .instr_sub
  | .instr_beq => .decoder .instr_beq
  | .instr_bne => .decoder .instr_bne
  | .instr_bge => .decoder .instr_bge
  | .instr_bgeu => .decoder .instr_bgeu
  | .instr_xori => .decoder .instr_xori
  | .instr_xor => .decoder .instr_xor
  | .instr_ori => .decoder .instr_ori
  | .instr_or => .decoder .instr_or
  | .instr_andi => .decoder .instr_andi
  | .instr_and => .decoder .instr_and
  | .instr_slli => .decoder .instr_slli
  | .instr_srli => .decoder .instr_srli
  | .instr_srai => .decoder .instr_srai
  | .instr_sll => .decoder .instr_sll
  | .instr_srl => .decoder .instr_srl
  | .instr_sra => .decoder .instr_sra
  | .is_lui_auipc_jal => .decoder .is_lui_auipc_jal
  | .is_lb_lh_lw_lbu_lhu => .decoder .is_lb_lh_lw_lbu_lhu
  | .is_slli_srli_srai => .decoder .is_slli_srli_srai
  | .is_jalr_addi_slti_sltiu_xori_ori_andi =>
      .decoder .is_jalr_addi_slti_sltiu_xori_ori_andi
  | .is_lui_auipc_jal_jalr_addi_add_sub =>
      .decoder .is_lui_auipc_jal_jalr_addi_add_sub
  | .is_slti_blt_slt => .decoder .is_slti_blt_slt
  | .is_sltiu_bltu_sltu => .decoder .is_sltiu_bltu_sltu
  | .is_compare => .decoder .is_compare
  | .decoded_imm => .decoder .decoded_imm
  | .decoded_imm_j => .decoder .decoded_imm_j
  | .decoded_rs2 => .decoder .decoded_rs2
  | .cpuregs_rs1 => .regs .cpuregs_rs1
  | .cpuregs_rs2 => .regs .cpuregs_rs2
  | .mem_done => .memory .mem_done
  | .mem_rdata_word => .memory .mem_rdata_word

def memorySource : P.Memory.Input → SourcePort
  | .resetn => .resetn
  | .trap => .control .trap
  | .mem_do_prefetch => .control .mem_do_prefetch
  | .mem_do_rinst => .control .mem_do_rinst
  | .mem_do_rdata => .control .mem_do_rdata
  | .mem_do_wdata => .control .mem_do_wdata
  | .next_pc => .datapath .next_pc
  | .reg_op1 => .datapath .reg_op1
  | .reg_op2 => .datapath .reg_op2
  | .mem_wordsize => .control .mem_wordsize
  | .mem_ready => .mem_ready
  | .mem_rdata => .mem_rdata

def decoderSource : P.Decoder.Input → SourcePort
  | .resetn => .resetn
  | .mem_do_rinst => .control .mem_do_rinst
  | .mem_done => .memory .mem_done
  | .mem_rdata_latched => .memory .mem_rdata_latched
  | .decoder_trigger => .control .decoder_trigger
  | .decoder_pseudo_trigger => .control .decoder_pseudo_trigger
  | .mem_rdata_q => .memory .mem_rdata_q

def regsSource : P.Regs.Input → SourcePort
  | .resetn => .resetn
  | .decoded_rs1 => .decoder .decoded_rs1
  | .decoded_rs2 => .decoder .decoded_rs2
  | .cpuregs_write => .control .cpuregs_write
  | .latched_rd => .control .latched_rd
  | .cpuregs_wrdata => .datapath .cpuregs_wrdata

example (input : P.Control.Input) :
    P.Control.inputMap.signalType input = sourceType (controlSource input) := by
  cases input <;> rfl

example (input : P.Datapath.Input) :
    P.Datapath.inputMap.signalType input = sourceType (datapathSource input) := by
  cases input <;> rfl

example (input : P.Memory.Input) :
    P.Memory.inputMap.signalType input = sourceType (memorySource input) := by
  cases input <;> rfl

example (input : P.Decoder.Input) :
    P.Decoder.inputMap.signalType input = sourceType (decoderSource input) := by
  cases input <;> rfl

example (input : P.Regs.Input) :
    P.Regs.inputMap.signalType input = sourceType (regsSource input) := by
  cases input <;> rfl

end Silean.Examples.Checks.PicoRVBoundary
