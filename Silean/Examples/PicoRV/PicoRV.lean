import Silean.Contracts.Cycle.CycleBlackbox
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Examples.PicoRV.Control
import Silean.Examples.PicoRV.Datapath
import Silean.Examples.PicoRV.Decoder
import Silean.Examples.PicoRV.Memory
import Silean.Examples.PicoRV.Regs

namespace Silean.Examples.PicoRV.PicoRV

open Silean

/-! The configured PicoRV32 top-level hardware boundary. Its five children are
behavioral blackboxes at this stage: their reviewed cycle contracts define the
equations used to check this composition, but none is presented as a completed
structural implementation. -/

inductive Input
  | resetn
  | mem_ready
  | mem_rdata
deriving Enumeration

inductive Output
  | trap
  | mem_valid | mem_instr | mem_addr | mem_wdata | mem_wstrb
  | mem_la_read | mem_la_write | mem_la_addr | mem_la_wdata | mem_la_wstrb
deriving Enumeration

@[reducible] def inputMap : SignalMap :=
  EnumeratedMap.of Input fun
    | .resetn | .mem_ready => .bit
    | .mem_rdata => .vector 32 .bit

@[reducible] def outputMap : SignalMap :=
  EnumeratedMap.of Output fun
    | .trap | .mem_valid | .mem_instr | .mem_la_read | .mem_la_write => .bit
    | .mem_wstrb | .mem_la_wstrb => .vector 4 .bit
    | .mem_addr | .mem_wdata | .mem_la_addr | .mem_la_wdata => .vector 32 .bit

@[reducible] def ports : ModulePorts := ⟨inputMap, outputMap⟩

/-! The direct children follow the reviewed source-region split. -/
inductive Instance
  | control
  | datapath
  | mem
  | decoder
  | cpuregs
deriving Enumeration

@[reducible] def instancePorts : InstancePorts :=
  EnumeratedMap.of Instance fun
    | .control => Control.ports
    | .datapath => Datapath.ports
    | .mem => Memory.ports
    | .decoder => Decoder.ports
    | .cpuregs => Regs.ports

@[reducible] def context : EndpointContext where
  ports := ports
  instancePorts := instancePorts

/-! Every sink has exactly one typed source. Signals shared by several regions
fan out directly; they are not forwarded through the control child. -/
def wiring : Wiring context.ports context.instancePorts where
  moduleOutput := fun
    -- The registered trap output belongs to control.
    | .trap => context.instanceOutput .control .trap
    -- The ordinary and look-ahead memory interfaces belong to `mem`.
    | .mem_valid => context.instanceOutput .mem .mem_valid
    | .mem_instr => context.instanceOutput .mem .mem_instr
    | .mem_addr => context.instanceOutput .mem .mem_addr
    | .mem_wdata => context.instanceOutput .mem .mem_wdata
    | .mem_wstrb => context.instanceOutput .mem .mem_wstrb
    | .mem_la_read => context.instanceOutput .mem .mem_la_read
    | .mem_la_write => context.instanceOutput .mem .mem_la_write
    | .mem_la_addr => context.instanceOutput .mem .mem_la_addr
    | .mem_la_wdata => context.instanceOutput .mem .mem_la_wdata
    | .mem_la_wstrb => context.instanceOutput .mem .mem_la_wstrb
  instanceInput := fun
    -- Control observes reset, decoded instruction classes, datapath decisions,
    -- and memory completion.
    | .control, .resetn => context.moduleInput .resetn
    | .control, .instr_jal => context.instanceOutput .decoder .instr_jal
    | .control, .instr_jalr => context.instanceOutput .decoder .instr_jalr
    | .control, .instr_lb => context.instanceOutput .decoder .instr_lb
    | .control, .instr_lbu => context.instanceOutput .decoder .instr_lbu
    | .control, .instr_lh => context.instanceOutput .decoder .instr_lh
    | .control, .instr_lhu => context.instanceOutput .decoder .instr_lhu
    | .control, .instr_lw => context.instanceOutput .decoder .instr_lw
    | .control, .instr_sb => context.instanceOutput .decoder .instr_sb
    | .control, .instr_sh => context.instanceOutput .decoder .instr_sh
    | .control, .instr_sw => context.instanceOutput .decoder .instr_sw
    | .control, .instr_trap => context.instanceOutput .decoder .instr_trap
    | .control, .is_lui_auipc_jal => context.instanceOutput .decoder .is_lui_auipc_jal
    | .control, .is_lb_lh_lw_lbu_lhu =>
        context.instanceOutput .decoder .is_lb_lh_lw_lbu_lhu
    | .control, .is_slli_srli_srai =>
        context.instanceOutput .decoder .is_slli_srli_srai
    | .control, .is_jalr_addi_slti_sltiu_xori_ori_andi =>
        context.instanceOutput .decoder .is_jalr_addi_slti_sltiu_xori_ori_andi
    | .control, .is_sb_sh_sw => context.instanceOutput .decoder .is_sb_sh_sw
    | .control, .is_sll_srl_sra => context.instanceOutput .decoder .is_sll_srl_sra
    | .control, .is_beq_bne_blt_bge_bltu_bgeu =>
        context.instanceOutput .decoder .is_beq_bne_blt_bge_bltu_bgeu
    | .control, .is_lbu_lhu_lw => context.instanceOutput .decoder .is_lbu_lhu_lw
    | .control, .decoded_rd => context.instanceOutput .decoder .decoded_rd
    | .control, .reg_pc => context.instanceOutput .datapath .reg_pc
    | .control, .reg_op1 => context.instanceOutput .datapath .reg_op1
    | .control, .reg_sh => context.instanceOutput .datapath .reg_sh
    | .control, .alu_out_0 => context.instanceOutput .datapath .alu_out_0
    | .control, .mem_done => context.instanceOutput .mem .mem_done

    -- Datapath state advances under registered control, decoded selectors,
    -- register-file reads, and completed memory data.
    | .datapath, .resetn => context.moduleInput .resetn
    | .datapath, .cpu_state => context.instanceOutput .control .cpu_state
    | .datapath, .latched_store => context.instanceOutput .control .latched_store
    | .datapath, .latched_stalu => context.instanceOutput .control .latched_stalu
    | .datapath, .latched_branch => context.instanceOutput .control .latched_branch
    | .datapath, .latched_is_lu => context.instanceOutput .control .latched_is_lu
    | .datapath, .latched_is_lh => context.instanceOutput .control .latched_is_lh
    | .datapath, .latched_is_lb => context.instanceOutput .control .latched_is_lb
    | .datapath, .mem_do_prefetch => context.instanceOutput .control .mem_do_prefetch
    | .datapath, .mem_do_rdata => context.instanceOutput .control .mem_do_rdata
    | .datapath, .mem_do_wdata => context.instanceOutput .control .mem_do_wdata
    | .datapath, .decoder_trigger => context.instanceOutput .control .decoder_trigger
    | .datapath, .instr_lui => context.instanceOutput .decoder .instr_lui
    | .datapath, .instr_jal => context.instanceOutput .decoder .instr_jal
    | .datapath, .instr_sub => context.instanceOutput .decoder .instr_sub
    | .datapath, .instr_beq => context.instanceOutput .decoder .instr_beq
    | .datapath, .instr_bne => context.instanceOutput .decoder .instr_bne
    | .datapath, .instr_bge => context.instanceOutput .decoder .instr_bge
    | .datapath, .instr_bgeu => context.instanceOutput .decoder .instr_bgeu
    | .datapath, .instr_xori => context.instanceOutput .decoder .instr_xori
    | .datapath, .instr_xor => context.instanceOutput .decoder .instr_xor
    | .datapath, .instr_ori => context.instanceOutput .decoder .instr_ori
    | .datapath, .instr_or => context.instanceOutput .decoder .instr_or
    | .datapath, .instr_andi => context.instanceOutput .decoder .instr_andi
    | .datapath, .instr_and => context.instanceOutput .decoder .instr_and
    | .datapath, .instr_slli => context.instanceOutput .decoder .instr_slli
    | .datapath, .instr_srli => context.instanceOutput .decoder .instr_srli
    | .datapath, .instr_srai => context.instanceOutput .decoder .instr_srai
    | .datapath, .instr_sll => context.instanceOutput .decoder .instr_sll
    | .datapath, .instr_srl => context.instanceOutput .decoder .instr_srl
    | .datapath, .instr_sra => context.instanceOutput .decoder .instr_sra
    | .datapath, .is_lui_auipc_jal => context.instanceOutput .decoder .is_lui_auipc_jal
    | .datapath, .is_lb_lh_lw_lbu_lhu =>
        context.instanceOutput .decoder .is_lb_lh_lw_lbu_lhu
    | .datapath, .is_slli_srli_srai =>
        context.instanceOutput .decoder .is_slli_srli_srai
    | .datapath, .is_jalr_addi_slti_sltiu_xori_ori_andi =>
        context.instanceOutput .decoder .is_jalr_addi_slti_sltiu_xori_ori_andi
    | .datapath, .is_lui_auipc_jal_jalr_addi_add_sub =>
        context.instanceOutput .decoder .is_lui_auipc_jal_jalr_addi_add_sub
    | .datapath, .is_slti_blt_slt => context.instanceOutput .decoder .is_slti_blt_slt
    | .datapath, .is_sltiu_bltu_sltu =>
        context.instanceOutput .decoder .is_sltiu_bltu_sltu
    | .datapath, .is_compare => context.instanceOutput .decoder .is_compare
    | .datapath, .decoded_imm => context.instanceOutput .decoder .decoded_imm
    | .datapath, .decoded_imm_j => context.instanceOutput .decoder .decoded_imm_j
    | .datapath, .decoded_rs2 => context.instanceOutput .decoder .decoded_rs2
    | .datapath, .cpuregs_rs1 => context.instanceOutput .cpuregs .cpuregs_rs1
    | .datapath, .cpuregs_rs2 => context.instanceOutput .cpuregs .cpuregs_rs2
    | .datapath, .mem_done => context.instanceOutput .mem .mem_done
    | .datapath, .mem_rdata_word => context.instanceOutput .mem .mem_rdata_word

    -- Memory receives commands from control, address/data values from the
    -- datapath, and the external ready/read-data interface.
    | .mem, .resetn => context.moduleInput .resetn
    | .mem, .trap => context.instanceOutput .control .trap
    | .mem, .mem_do_prefetch => context.instanceOutput .control .mem_do_prefetch
    | .mem, .mem_do_rinst => context.instanceOutput .control .mem_do_rinst
    | .mem, .mem_do_rdata => context.instanceOutput .control .mem_do_rdata
    | .mem, .mem_do_wdata => context.instanceOutput .control .mem_do_wdata
    | .mem, .next_pc => context.instanceOutput .datapath .next_pc
    | .mem, .reg_op1 => context.instanceOutput .datapath .reg_op1
    | .mem, .reg_op2 => context.instanceOutput .datapath .reg_op2
    | .mem, .mem_wordsize => context.instanceOutput .control .mem_wordsize
    | .mem, .mem_ready => context.moduleInput .mem_ready
    | .mem, .mem_rdata => context.moduleInput .mem_rdata

    -- Decoder consumes the memory response under control's registered trigger.
    | .decoder, .resetn => context.moduleInput .resetn
    | .decoder, .mem_do_rinst => context.instanceOutput .control .mem_do_rinst
    | .decoder, .mem_done => context.instanceOutput .mem .mem_done
    | .decoder, .mem_rdata_latched => context.instanceOutput .mem .mem_rdata_latched
    | .decoder, .decoder_trigger => context.instanceOutput .control .decoder_trigger
    | .decoder, .decoder_pseudo_trigger =>
        context.instanceOutput .control .decoder_pseudo_trigger
    | .decoder, .mem_rdata_q => context.instanceOutput .mem .mem_rdata_q

    -- The register file reads decoder addresses and writes the datapath result
    -- under control's write enable and registered destination.
    | .cpuregs, .resetn => context.moduleInput .resetn
    | .cpuregs, .decoded_rs1 => context.instanceOutput .decoder .decoded_rs1
    | .cpuregs, .decoded_rs2 => context.instanceOutput .decoder .decoded_rs2
    | .cpuregs, .cpuregs_write => context.instanceOutput .control .cpuregs_write
    | .cpuregs, .latched_rd => context.instanceOutput .control .latched_rd
    | .cpuregs, .cpuregs_wrdata => context.instanceOutput .datapath .cpuregs_wrdata

@[reducible] def body : ModuleBody := ⟨context, wiring⟩

@[reducible] def childContracts : Contracts.Cycle.ChildCycleContracts body
  | .control => Control.cycleContract
  | .datapath => Datapath.cycleContract
  | .mem => Memory.cycleContract
  | .decoder => Decoder.cycleContract
  | .cpuregs => Regs.cycleContract

@[reducible] def children : Contracts.Cycle.Certification.Layer.ChildStructures
    body childContracts
  | .control => Control.cycleContract.blackboxCertified.certifiedStructure
  | .datapath => Datapath.cycleContract.blackboxCertified.certifiedStructure
  | .mem => Memory.cycleContract.blackboxCertified.certifiedStructure
  | .decoder => Decoder.cycleContract.blackboxCertified.certifiedStructure
  | .cpuregs => Regs.cycleContract.blackboxCertified.certifiedStructure

/-! The top-level structure is real wiring around explicitly opaque children. -/
def moduleStructure : ModuleStructure ports :=
  Contracts.Cycle.Certification.Layer.moduleStructure body children

end Silean.Examples.PicoRV.PicoRV
