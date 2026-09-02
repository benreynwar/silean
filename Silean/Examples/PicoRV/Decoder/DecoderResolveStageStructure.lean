import Silean.Examples.PicoRV.Decoder.DecoderResolveStage
import Silean.Examples.PicoRV.Decoder.DecoderInstructionMatch
import Silean.Examples.PicoRV.Decoder.DecoderImmediate
import Silean.Examples.PicoRV.Decoder.DecoderInstructionSummary
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleBlackbox
import Silean.Modules.EnabledRegister
import Silean.Modules.EnabledResetRegister
import Silean.Modules.Register
import Silean.Modules.ResetRegister
import Silean.Modules.Mux
import Silean.Modules.Constant
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming

namespace Silean.Examples.PicoRV.Decoder.ResolveStage

open Silean
open Silean.Examples.PicoRV.Decoder

/-! ## Structural implementation

The 45 logical contract registers are grouped into six aggregate storage
instances. This grouping is structural only: `stateCorresponds` below maps
every contract field explicitly, so the public contract retains the source
Verilog's individual state names and update behavior.

The three combinational decoder children remain explicit blackboxes at this
stage. Their public contracts, rather than their future implementations, are
the only facts used by this parent. -/

private def resetMatchRegisters : List Register := [
  .instr_beq, .instr_bne, .instr_blt, .instr_bge, .instr_bltu, .instr_bgeu,
  .instr_addi, .instr_slti, .instr_sltiu, .instr_xori, .instr_ori, .instr_andi,
  .instr_add, .instr_sub, .instr_sll, .instr_slt, .instr_sltu, .instr_xor,
  .instr_srl, .instr_sra, .instr_or, .instr_and, .instr_fence]

private def retainedMatchRegisters : List Register := [
  .instr_lb, .instr_lh, .instr_lw, .instr_lbu, .instr_lhu,
  .instr_sb, .instr_sh, .instr_sw,
  .instr_slli, .instr_srli, .instr_srai, .instr_ecall_ebreak,
  .is_slli_srli_srai, .is_jalr_addi_slti_sltiu_xori_ori_andi,
  .is_sll_srl_sra]

private def ordinarySummaryRegisters : List Register := [
  .is_lui_auipc_jal, .is_slti_blt_slt, .is_sltiu_bltu_sltu, .is_lbu_lhu_lw]

@[simp] private theorem resetMatchRegisters_length : resetMatchRegisters.length = 23 := rfl
@[simp] private theorem retainedMatchRegisters_length : retainedMatchRegisters.length = 15 := rfl
@[simp] private theorem ordinarySummaryRegisters_length : ordinarySummaryRegisters.length = 4 := rfl

private def resetMatchRegister (index : Fin 23) : Register :=
  resetMatchRegisters[index]

private def retainedMatchRegister (index : Fin 15) : Register :=
  retainedMatchRegisters[index]

private def ordinarySummaryRegister (index : Fin 4) : Register :=
  ordinarySummaryRegisters[index]

private theorem resetMatchRegister_bit : ∀ index : Fin 23,
    registerType (resetMatchRegister index) = .bit := by native_decide

private theorem retainedMatchRegister_bit : ∀ index : Fin 15,
    registerType (retainedMatchRegister index) = .bit := by native_decide

private theorem ordinarySummaryRegister_bit : ∀ index : Fin 4,
    registerType (ordinarySummaryRegister index) = .bit := by native_decide

private def resetMatchType : SignalType := .vector 23 .bit
private def retainedMatchType : SignalType := .vector 15 .bit
private def ordinarySummaryType : SignalType := .vector 4 .bit

private def resetMatchValue (state : stateMap.Values) : resetMatchType.Denote :=
  fun index => cast (congrArg SignalType.Denote (resetMatchRegister_bit index))
    (state (resetMatchRegister index))

private def retainedMatchValue (state : stateMap.Values) : retainedMatchType.Denote :=
  fun index => cast (congrArg SignalType.Denote (retainedMatchRegister_bit index))
    (state (retainedMatchRegister index))

private def ordinarySummaryValue (state : stateMap.Values) : ordinarySummaryType.Denote :=
  fun index => cast (congrArg SignalType.Denote (ordinarySummaryRegister_bit index))
    (state (ordinarySummaryRegister index))

private def falseResetMatches : resetMatchType.Denote := fun _ => false

private def matchOutput : Register → InstructionMatch.Output
  | .instr_beq => .instr_beq | .instr_bne => .instr_bne
  | .instr_blt => .instr_blt | .instr_bge => .instr_bge
  | .instr_bltu => .instr_bltu | .instr_bgeu => .instr_bgeu
  | .instr_lb => .instr_lb | .instr_lh => .instr_lh
  | .instr_lw => .instr_lw | .instr_lbu => .instr_lbu
  | .instr_lhu => .instr_lhu
  | .instr_sb => .instr_sb | .instr_sh => .instr_sh | .instr_sw => .instr_sw
  | .instr_addi => .instr_addi | .instr_slti => .instr_slti
  | .instr_sltiu => .instr_sltiu | .instr_xori => .instr_xori
  | .instr_ori => .instr_ori | .instr_andi => .instr_andi
  | .instr_slli => .instr_slli | .instr_srli => .instr_srli
  | .instr_srai => .instr_srai
  | .instr_add => .instr_add | .instr_sub => .instr_sub
  | .instr_sll => .instr_sll | .instr_slt => .instr_slt
  | .instr_sltu => .instr_sltu | .instr_xor => .instr_xor
  | .instr_srl => .instr_srl | .instr_sra => .instr_sra
  | .instr_or => .instr_or | .instr_and => .instr_and
  | .instr_ecall_ebreak => .instr_ecall_ebreak | .instr_fence => .instr_fence
  | .is_slli_srli_srai => .is_slli_srli_srai
  | .is_jalr_addi_slti_sltiu_xori_ori_andi =>
      .is_jalr_addi_slti_sltiu_xori_ori_andi
  | .is_sll_srl_sra => .is_sll_srl_sra
  | .decoded_imm | .is_lui_auipc_jal |
      .is_lui_auipc_jal_jalr_addi_add_sub | .is_slti_blt_slt |
      .is_sltiu_bltu_sltu | .is_lbu_lhu_lw | .is_compare =>
      .instr_fence -- unreachable for the two match-register groups

private def summaryOutput : Register → InstructionSummary.Output
  | .is_lui_auipc_jal => .is_lui_auipc_jal
  | .is_lui_auipc_jal_jalr_addi_add_sub => .is_lui_auipc_jal_jalr_addi_add_sub
  | .is_slti_blt_slt => .is_slti_blt_slt
  | .is_sltiu_bltu_sltu => .is_sltiu_bltu_sltu
  | .is_lbu_lhu_lw => .is_lbu_lhu_lw
  | .is_compare => .is_compare
  | _ => .instr_trap -- unreachable for summary registers

inductive Instance
  /-- `decoder_trigger && !decoder_pseudo_trigger`. -/
  | pseudoInverter | triggerEnable
  /-- Active-high internal reset derived from the active-low port. -/
  | resetInverter
  /-- Contract-only combinational decoder children. -/
  | instructionMatch | immediate | instructionSummary
  /-- Assemble child results into aggregate register inputs. -/
  | resetMatchNext | retainedMatchNext | ordinarySummaryNext
  /-- Stateful storage groups. -/
  | resetMatchStorage | retainedMatchStorage | immediateStorage
  | ordinarySummaryStorage | addSubSummaryStorage | compareStorage
  /-- Immediate retention and trigger-overridden summary selection. -/
  | immediateSelection | addSubSummarySelection | compareSelection
  /-- Expose aggregate stored fields. -/
  | resetMatchOutputs | retainedMatchOutputs | ordinarySummaryOutputs
  /-- Shared false value for trigger overrides. -/
  | falseValue
deriving Enumeration

private def resetMatchCombiner : Composition.SignalCombiner := .vector 23 .bit
private def retainedMatchCombiner : Composition.SignalCombiner := .vector 15 .bit
private def ordinarySummaryCombiner : Composition.SignalCombiner := .vector 4 .bit
private def resetMatchSplitter : Composition.SignalSplitter := .vector 23 .bit
private def retainedMatchSplitter : Composition.SignalSplitter := .vector 15 .bit
private def ordinarySummarySplitter : Composition.SignalSplitter := .vector 4 .bit

@[reducible] def instancePorts : InstancePorts := EnumeratedMap.of Instance fun
  | .pseudoInverter | .resetInverter => Primitives.not.ports
  | .triggerEnable => Primitives.and.ports
  | .instructionMatch => InstructionMatch.ports
  | .immediate => Immediate.ports
  | .instructionSummary => InstructionSummary.ports
  | .resetMatchNext => resetMatchCombiner.ports
  | .retainedMatchNext => retainedMatchCombiner.ports
  | .ordinarySummaryNext => ordinarySummaryCombiner.ports
  | .resetMatchStorage => Modules.EnabledResetRegister.ports resetMatchType
  | .retainedMatchStorage => Modules.EnabledRegister.ports retainedMatchType
  | .immediateStorage => Modules.EnabledRegister.ports (.vector 32 .bit)
  | .ordinarySummaryStorage => Modules.Register.ports ordinarySummaryType
  | .addSubSummaryStorage => Modules.Register.ports .bit
  | .compareStorage => Modules.ResetRegister.ports .bit
  | .immediateSelection => Modules.Mux.ports (.vector 32 .bit)
  | .addSubSummarySelection | .compareSelection => Modules.Mux.ports .bit
  | .resetMatchOutputs => resetMatchSplitter.ports
  | .retainedMatchOutputs => retainedMatchSplitter.ports
  | .ordinarySummaryOutputs => ordinarySummarySplitter.ports
  | .falseValue => Modules.Constant.ports .bit

@[reducible] def context : EndpointContext where
  ports := ports
  instancePorts := instancePorts

private def resetPosition : Register → Option (Fin 23)
  | .instr_beq => some 0 | .instr_bne => some 1 | .instr_blt => some 2
  | .instr_bge => some 3 | .instr_bltu => some 4 | .instr_bgeu => some 5
  | .instr_addi => some 6 | .instr_slti => some 7 | .instr_sltiu => some 8
  | .instr_xori => some 9 | .instr_ori => some 10 | .instr_andi => some 11
  | .instr_add => some 12 | .instr_sub => some 13 | .instr_sll => some 14
  | .instr_slt => some 15 | .instr_sltu => some 16 | .instr_xor => some 17
  | .instr_srl => some 18 | .instr_sra => some 19 | .instr_or => some 20
  | .instr_and => some 21 | .instr_fence => some 22
  | _ => none

private def retainedPosition : Register → Option (Fin 15)
  | .instr_lb => some 0 | .instr_lh => some 1 | .instr_lw => some 2
  | .instr_lbu => some 3 | .instr_lhu => some 4
  | .instr_sb => some 5 | .instr_sh => some 6 | .instr_sw => some 7
  | .instr_slli => some 8 | .instr_srli => some 9 | .instr_srai => some 10
  | .instr_ecall_ebreak => some 11 | .is_slli_srli_srai => some 12
  | .is_jalr_addi_slti_sltiu_xori_ori_andi => some 13
  | .is_sll_srl_sra => some 14
  | _ => none

private def ordinarySummaryPosition : Register → Option (Fin 4)
  | .is_lui_auipc_jal => some 0 | .is_slti_blt_slt => some 1
  | .is_sltiu_bltu_sltu => some 2 | .is_lbu_lhu_lw => some 3
  | _ => none

private def resetStoredBit (index : Fin 23) :
    SignalSource context.ports context.instancePorts .bit :=
  context.instanceOutput .resetMatchOutputs index

private def retainedStoredBit (index : Fin 15) :
    SignalSource context.ports context.instancePorts .bit :=
  context.instanceOutput .retainedMatchOutputs index

private def ordinarySummaryStoredBit (index : Fin 4) :
    SignalSource context.ports context.instancePorts .bit :=
  context.instanceOutput .ordinarySummaryOutputs index

private def storedSource : (register : Register) →
    SignalSource context.ports context.instancePorts (registerType register)
  | .instr_beq => resetStoredBit 0 | .instr_bne => resetStoredBit 1
  | .instr_blt => resetStoredBit 2 | .instr_bge => resetStoredBit 3
  | .instr_bltu => resetStoredBit 4 | .instr_bgeu => resetStoredBit 5
  | .instr_addi => resetStoredBit 6 | .instr_slti => resetStoredBit 7
  | .instr_sltiu => resetStoredBit 8 | .instr_xori => resetStoredBit 9
  | .instr_ori => resetStoredBit 10 | .instr_andi => resetStoredBit 11
  | .instr_add => resetStoredBit 12 | .instr_sub => resetStoredBit 13
  | .instr_sll => resetStoredBit 14 | .instr_slt => resetStoredBit 15
  | .instr_sltu => resetStoredBit 16 | .instr_xor => resetStoredBit 17
  | .instr_srl => resetStoredBit 18 | .instr_sra => resetStoredBit 19
  | .instr_or => resetStoredBit 20 | .instr_and => resetStoredBit 21
  | .instr_fence => resetStoredBit 22
  | .instr_lb => retainedStoredBit 0 | .instr_lh => retainedStoredBit 1
  | .instr_lw => retainedStoredBit 2 | .instr_lbu => retainedStoredBit 3
  | .instr_lhu => retainedStoredBit 4 | .instr_sb => retainedStoredBit 5
  | .instr_sh => retainedStoredBit 6 | .instr_sw => retainedStoredBit 7
  | .instr_slli => retainedStoredBit 8 | .instr_srli => retainedStoredBit 9
  | .instr_srai => retainedStoredBit 10
  | .instr_ecall_ebreak => retainedStoredBit 11
  | .is_slli_srli_srai => retainedStoredBit 12
  | .is_jalr_addi_slti_sltiu_xori_ori_andi =>
      retainedStoredBit 13
  | .is_sll_srl_sra => retainedStoredBit 14
  | .decoded_imm => context.instanceOutput .immediateStorage .value
  | .is_lui_auipc_jal => ordinarySummaryStoredBit 0
  | .is_slti_blt_slt => ordinarySummaryStoredBit 1
  | .is_sltiu_bltu_sltu => ordinarySummaryStoredBit 2
  | .is_lbu_lhu_lw => ordinarySummaryStoredBit 3
  | .is_lui_auipc_jal_jalr_addi_add_sub =>
      context.instanceOutput .addSubSummaryStorage .output
  | .is_compare => context.instanceOutput .compareStorage .value

private def outputRegister : Output → Option Register
  | .instr_trap => none
  | .instr_beq => some .instr_beq | .instr_bne => some .instr_bne
  | .instr_blt => some .instr_blt | .instr_bge => some .instr_bge
  | .instr_bltu => some .instr_bltu | .instr_bgeu => some .instr_bgeu
  | .instr_lb => some .instr_lb | .instr_lh => some .instr_lh
  | .instr_lw => some .instr_lw | .instr_lbu => some .instr_lbu
  | .instr_lhu => some .instr_lhu | .instr_sb => some .instr_sb
  | .instr_sh => some .instr_sh | .instr_sw => some .instr_sw
  | .instr_addi => some .instr_addi | .instr_slti => some .instr_slti
  | .instr_sltiu => some .instr_sltiu | .instr_xori => some .instr_xori
  | .instr_ori => some .instr_ori | .instr_andi => some .instr_andi
  | .instr_slli => some .instr_slli | .instr_srli => some .instr_srli
  | .instr_srai => some .instr_srai | .instr_add => some .instr_add
  | .instr_sub => some .instr_sub | .instr_sll => some .instr_sll
  | .instr_slt => some .instr_slt | .instr_sltu => some .instr_sltu
  | .instr_xor => some .instr_xor | .instr_srl => some .instr_srl
  | .instr_sra => some .instr_sra | .instr_or => some .instr_or
  | .instr_and => some .instr_and | .instr_fence => some .instr_fence
  | .decoded_imm => some .decoded_imm
  | .is_lui_auipc_jal => some .is_lui_auipc_jal
  | .is_slli_srli_srai => some .is_slli_srli_srai
  | .is_jalr_addi_slti_sltiu_xori_ori_andi =>
      some .is_jalr_addi_slti_sltiu_xori_ori_andi
  | .is_sll_srl_sra => some .is_sll_srl_sra
  | .is_lui_auipc_jal_jalr_addi_add_sub =>
      some .is_lui_auipc_jal_jalr_addi_add_sub
  | .is_slti_blt_slt => some .is_slti_blt_slt
  | .is_sltiu_bltu_sltu => some .is_sltiu_bltu_sltu
  | .is_lbu_lhu_lw => some .is_lbu_lhu_lw
  | .is_compare => some .is_compare

private def summaryInputRegister : InstructionSummary.Input → Option Register
  | .instr_lui | .instr_auipc | .instr_jal | .instr_jalr |
      .is_beq_bne_blt_bge_bltu_bgeu => none
  | .instr_beq => some .instr_beq | .instr_bne => some .instr_bne
  | .instr_blt => some .instr_blt | .instr_bge => some .instr_bge
  | .instr_bltu => some .instr_bltu | .instr_bgeu => some .instr_bgeu
  | .instr_lb => some .instr_lb | .instr_lh => some .instr_lh
  | .instr_lw => some .instr_lw | .instr_lbu => some .instr_lbu
  | .instr_lhu => some .instr_lhu | .instr_sb => some .instr_sb
  | .instr_sh => some .instr_sh | .instr_sw => some .instr_sw
  | .instr_addi => some .instr_addi | .instr_slti => some .instr_slti
  | .instr_sltiu => some .instr_sltiu | .instr_xori => some .instr_xori
  | .instr_ori => some .instr_ori | .instr_andi => some .instr_andi
  | .instr_slli => some .instr_slli | .instr_srli => some .instr_srli
  | .instr_srai => some .instr_srai | .instr_add => some .instr_add
  | .instr_sub => some .instr_sub | .instr_sll => some .instr_sll
  | .instr_slt => some .instr_slt | .instr_sltu => some .instr_sltu
  | .instr_xor => some .instr_xor | .instr_srl => some .instr_srl
  | .instr_sra => some .instr_sra | .instr_or => some .instr_or
  | .instr_and => some .instr_and | .instr_ecall_ebreak => some .instr_ecall_ebreak
  | .instr_fence => some .instr_fence

def wiring : Wiring context.ports context.instancePorts where
  moduleOutput
    | .instr_trap => context.instanceOutput .instructionSummary .instr_trap
    | .instr_beq => storedSource .instr_beq | .instr_bne => storedSource .instr_bne
    | .instr_blt => storedSource .instr_blt | .instr_bge => storedSource .instr_bge
    | .instr_bltu => storedSource .instr_bltu | .instr_bgeu => storedSource .instr_bgeu
    | .instr_lb => storedSource .instr_lb | .instr_lh => storedSource .instr_lh
    | .instr_lw => storedSource .instr_lw | .instr_lbu => storedSource .instr_lbu
    | .instr_lhu => storedSource .instr_lhu
    | .instr_sb => storedSource .instr_sb | .instr_sh => storedSource .instr_sh
    | .instr_sw => storedSource .instr_sw
    | .instr_addi => storedSource .instr_addi | .instr_slti => storedSource .instr_slti
    | .instr_sltiu => storedSource .instr_sltiu | .instr_xori => storedSource .instr_xori
    | .instr_ori => storedSource .instr_ori | .instr_andi => storedSource .instr_andi
    | .instr_slli => storedSource .instr_slli | .instr_srli => storedSource .instr_srli
    | .instr_srai => storedSource .instr_srai
    | .instr_add => storedSource .instr_add | .instr_sub => storedSource .instr_sub
    | .instr_sll => storedSource .instr_sll | .instr_slt => storedSource .instr_slt
    | .instr_sltu => storedSource .instr_sltu | .instr_xor => storedSource .instr_xor
    | .instr_srl => storedSource .instr_srl | .instr_sra => storedSource .instr_sra
    | .instr_or => storedSource .instr_or | .instr_and => storedSource .instr_and
    | .instr_fence => storedSource .instr_fence
    | .decoded_imm => storedSource .decoded_imm
    | .is_lui_auipc_jal => storedSource .is_lui_auipc_jal
    | .is_slli_srli_srai => storedSource .is_slli_srli_srai
    | .is_jalr_addi_slti_sltiu_xori_ori_andi =>
        storedSource .is_jalr_addi_slti_sltiu_xori_ori_andi
    | .is_sll_srl_sra => storedSource .is_sll_srl_sra
    | .is_lui_auipc_jal_jalr_addi_add_sub =>
        storedSource .is_lui_auipc_jal_jalr_addi_add_sub
    | .is_slti_blt_slt => storedSource .is_slti_blt_slt
    | .is_sltiu_bltu_sltu => storedSource .is_sltiu_bltu_sltu
    | .is_lbu_lhu_lw => storedSource .is_lbu_lhu_lw
    | .is_compare => storedSource .is_compare
  instanceInput
    | .pseudoInverter, .input => context.moduleInput .decoder_pseudo_trigger
    | .triggerEnable, .left => context.moduleInput .decoder_trigger
    | .triggerEnable, .right => context.instanceOutput .pseudoInverter .output
    | .resetInverter, .input => context.moduleInput .resetn
    | .instructionMatch, .word => context.moduleInput .mem_rdata_q
    | .instructionMatch, .instr_jalr => context.moduleInput .instr_jalr
    | .instructionMatch, .is_beq_bne_blt_bge_bltu_bgeu =>
        context.moduleInput .is_beq_bne_blt_bge_bltu_bgeu
    | .instructionMatch, .is_lb_lh_lw_lbu_lhu =>
        context.moduleInput .is_lb_lh_lw_lbu_lhu
    | .instructionMatch, .is_sb_sh_sw => context.moduleInput .is_sb_sh_sw
    | .instructionMatch, .is_alu_reg_imm => context.moduleInput .is_alu_reg_imm
    | .instructionMatch, .is_alu_reg_reg => context.moduleInput .is_alu_reg_reg
    | .immediate, .word => context.moduleInput .mem_rdata_q
    | .immediate, .decoded_imm_j => context.moduleInput .decoded_imm_j
    | .immediate, .instr_jal => context.moduleInput .instr_jal
    | .immediate, .instr_lui => context.moduleInput .instr_lui
    | .immediate, .instr_auipc => context.moduleInput .instr_auipc
    | .immediate, .instr_jalr => context.moduleInput .instr_jalr
    | .immediate, .is_lb_lh_lw_lbu_lhu => context.moduleInput .is_lb_lh_lw_lbu_lhu
    | .immediate, .is_alu_reg_imm => context.moduleInput .is_alu_reg_imm
    | .immediate, .is_beq_bne_blt_bge_bltu_bgeu =>
        context.moduleInput .is_beq_bne_blt_bge_bltu_bgeu
    | .immediate, .is_sb_sh_sw => context.moduleInput .is_sb_sh_sw
    | .instructionSummary, .instr_lui => context.moduleInput .instr_lui
    | .instructionSummary, .instr_auipc => context.moduleInput .instr_auipc
    | .instructionSummary, .instr_jal => context.moduleInput .instr_jal
    | .instructionSummary, .instr_jalr => context.moduleInput .instr_jalr
    | .instructionSummary, .is_beq_bne_blt_bge_bltu_bgeu =>
        context.moduleInput .is_beq_bne_blt_bge_bltu_bgeu
    | .instructionSummary, .instr_beq => storedSource .instr_beq
    | .instructionSummary, .instr_bne => storedSource .instr_bne
    | .instructionSummary, .instr_blt => storedSource .instr_blt
    | .instructionSummary, .instr_bge => storedSource .instr_bge
    | .instructionSummary, .instr_bltu => storedSource .instr_bltu
    | .instructionSummary, .instr_bgeu => storedSource .instr_bgeu
    | .instructionSummary, .instr_lb => storedSource .instr_lb
    | .instructionSummary, .instr_lh => storedSource .instr_lh
    | .instructionSummary, .instr_lw => storedSource .instr_lw
    | .instructionSummary, .instr_lbu => storedSource .instr_lbu
    | .instructionSummary, .instr_lhu => storedSource .instr_lhu
    | .instructionSummary, .instr_sb => storedSource .instr_sb
    | .instructionSummary, .instr_sh => storedSource .instr_sh
    | .instructionSummary, .instr_sw => storedSource .instr_sw
    | .instructionSummary, .instr_addi => storedSource .instr_addi
    | .instructionSummary, .instr_slti => storedSource .instr_slti
    | .instructionSummary, .instr_sltiu => storedSource .instr_sltiu
    | .instructionSummary, .instr_xori => storedSource .instr_xori
    | .instructionSummary, .instr_ori => storedSource .instr_ori
    | .instructionSummary, .instr_andi => storedSource .instr_andi
    | .instructionSummary, .instr_slli => storedSource .instr_slli
    | .instructionSummary, .instr_srli => storedSource .instr_srli
    | .instructionSummary, .instr_srai => storedSource .instr_srai
    | .instructionSummary, .instr_add => storedSource .instr_add
    | .instructionSummary, .instr_sub => storedSource .instr_sub
    | .instructionSummary, .instr_sll => storedSource .instr_sll
    | .instructionSummary, .instr_slt => storedSource .instr_slt
    | .instructionSummary, .instr_sltu => storedSource .instr_sltu
    | .instructionSummary, .instr_xor => storedSource .instr_xor
    | .instructionSummary, .instr_srl => storedSource .instr_srl
    | .instructionSummary, .instr_sra => storedSource .instr_sra
    | .instructionSummary, .instr_or => storedSource .instr_or
    | .instructionSummary, .instr_and => storedSource .instr_and
    | .instructionSummary, .instr_ecall_ebreak => storedSource .instr_ecall_ebreak
    | .instructionSummary, .instr_fence => storedSource .instr_fence
    | .resetMatchNext, index =>
        context.instanceOutput .instructionMatch (matchOutput (resetMatchRegister index))
    | .retainedMatchNext, index =>
        context.instanceOutput .instructionMatch (matchOutput (retainedMatchRegister index))
    | .ordinarySummaryNext, index =>
        context.instanceOutput .instructionSummary
          (summaryOutput (ordinarySummaryRegister index))
    | .resetMatchStorage, .value => context.instanceOutput .resetMatchNext .value
    | .resetMatchStorage, .enable => context.instanceOutput .triggerEnable .output
    | .resetMatchStorage, .reset => context.instanceOutput .resetInverter .output
    | .retainedMatchStorage, .value => context.instanceOutput .retainedMatchNext .value
    | .retainedMatchStorage, .enable => context.instanceOutput .triggerEnable .output
    | .immediateSelection, .select => context.instanceOutput .immediate .valid
    | .immediateSelection, .whenFalse => context.instanceOutput .immediateStorage .value
    | .immediateSelection, .whenTrue => context.instanceOutput .immediate .value
    | .immediateStorage, .value => context.instanceOutput .immediateSelection .result
    | .immediateStorage, .enable => context.instanceOutput .triggerEnable .output
    | .ordinarySummaryStorage, .input => context.instanceOutput .ordinarySummaryNext .value
    | .falseValue, impossible => nomatch impossible
    | .addSubSummarySelection, .select => context.instanceOutput .triggerEnable .output
    | .addSubSummarySelection, .whenFalse =>
        context.instanceOutput .instructionSummary .is_lui_auipc_jal_jalr_addi_add_sub
    | .addSubSummarySelection, .whenTrue => context.instanceOutput .falseValue .output
    | .addSubSummaryStorage, .input => context.instanceOutput .addSubSummarySelection .result
    | .compareSelection, .select => context.instanceOutput .triggerEnable .output
    | .compareSelection, .whenFalse => context.instanceOutput .instructionSummary .is_compare
    | .compareSelection, .whenTrue => context.instanceOutput .falseValue .output
    | .compareStorage, .value => context.instanceOutput .compareSelection .result
    | .compareStorage, .reset => context.instanceOutput .resetInverter .output
    | .resetMatchOutputs, .value => context.instanceOutput .resetMatchStorage .value
    | .retainedMatchOutputs, .value => context.instanceOutput .retainedMatchStorage .value
    | .ordinarySummaryOutputs, .value => context.instanceOutput .ordinarySummaryStorage .output

@[reducible] def body : ModuleBody := ⟨context, wiring⟩

@[reducible] def childContracts : Contracts.Cycle.ChildCycleContracts body
  | .pseudoInverter | .resetInverter => Primitives.notCycleContract
  | .triggerEnable => Primitives.andCycleContract
  | .instructionMatch => InstructionMatch.cycleContract
  | .immediate => Immediate.cycleContract
  | .instructionSummary => InstructionSummary.cycleContract
  | .resetMatchNext => resetMatchCombiner.cycleContract
  | .retainedMatchNext => retainedMatchCombiner.cycleContract
  | .ordinarySummaryNext => ordinarySummaryCombiner.cycleContract
  | .resetMatchStorage =>
      Modules.EnabledResetRegister.cycleContract resetMatchType falseResetMatches
  | .retainedMatchStorage => Modules.EnabledRegister.cycleContract retainedMatchType
  | .immediateStorage => Modules.EnabledRegister.cycleContract (.vector 32 .bit)
  | .ordinarySummaryStorage => Modules.Register.cycleContract ordinarySummaryType
  | .addSubSummaryStorage => Modules.Register.cycleContract .bit
  | .compareStorage => Modules.ResetRegister.cycleContract .bit false
  | .immediateSelection => Modules.Mux.cycleContract (.vector 32 .bit)
  | .addSubSummarySelection | .compareSelection => Modules.Mux.cycleContract .bit
  | .resetMatchOutputs => resetMatchSplitter.cycleContract
  | .retainedMatchOutputs => retainedMatchSplitter.cycleContract
  | .ordinarySummaryOutputs => ordinarySummarySplitter.cycleContract
  | .falseValue => Modules.Constant.cycleContract .bit false

@[reducible] def structuralChildren :
    (child : Instance) → ModuleStructure (instancePorts.ports child)
  | .pseudoInverter | .resetInverter => .primitive Primitives.not
  | .triggerEnable => .primitive Primitives.and
  | .instructionMatch => InstructionMatch.cycleContract.blackboxStructure
  | .immediate => Immediate.cycleContract.blackboxStructure
  | .instructionSummary => InstructionSummary.cycleContract.blackboxStructure
  | .resetMatchNext => .combiner resetMatchCombiner
  | .retainedMatchNext => .combiner retainedMatchCombiner
  | .ordinarySummaryNext => .combiner ordinarySummaryCombiner
  | .resetMatchStorage =>
      Modules.EnabledResetRegister.moduleStructure resetMatchType falseResetMatches
  | .retainedMatchStorage => Modules.EnabledRegister.moduleStructure retainedMatchType
  | .immediateStorage => Modules.EnabledRegister.moduleStructure (.vector 32 .bit)
  | .ordinarySummaryStorage => Modules.Register.moduleStructure ordinarySummaryType
  | .addSubSummaryStorage => Modules.Register.moduleStructure .bit
  | .compareStorage => Modules.ResetRegister.moduleStructure .bit false
  | .immediateSelection => Modules.Mux.moduleStructure (.vector 32 .bit)
  | .addSubSummarySelection | .compareSelection => Modules.Mux.moduleStructure .bit
  | .resetMatchOutputs => .splitter resetMatchSplitter
  | .retainedMatchOutputs => .splitter retainedMatchSplitter
  | .ordinarySummaryOutputs => .splitter ordinarySummarySplitter
  | .falseValue => Modules.Constant.moduleStructure .bit false

def moduleStructure : ModuleStructure ports := .composite body structuralChildren

@[reducible] noncomputable def certifiedChildren :
    (child : Instance) → Contracts.Cycle.ModuleCycleCertifiedStructure
      (childContracts child)
  | .pseudoInverter | .resetInverter =>
      ⟨.primitive Primitives.not, Primitives.notCertified.certification⟩
  | .triggerEnable =>
      ⟨.primitive Primitives.and, Primitives.andCertified.certification⟩
  | .instructionMatch => InstructionMatch.cycleContract.blackboxCertified.certifiedStructure
  | .immediate => Immediate.cycleContract.blackboxCertified.certifiedStructure
  | .instructionSummary => InstructionSummary.cycleContract.blackboxCertified.certifiedStructure
  | .resetMatchNext => resetMatchCombiner.certified.certifiedStructure
  | .retainedMatchNext => retainedMatchCombiner.certified.certifiedStructure
  | .ordinarySummaryNext => ordinarySummaryCombiner.certified.certifiedStructure
  | .resetMatchStorage =>
      (Modules.EnabledResetRegister.certified resetMatchType falseResetMatches).certifiedStructure
  | .retainedMatchStorage =>
      (Modules.EnabledRegister.certified retainedMatchType).certifiedStructure
  | .immediateStorage =>
      (Modules.EnabledRegister.certified (.vector 32 .bit)).certifiedStructure
  | .ordinarySummaryStorage =>
      (Modules.Register.certified ordinarySummaryType).certifiedStructure
  | .addSubSummaryStorage => (Modules.Register.certified .bit).certifiedStructure
  | .compareStorage => (Modules.ResetRegister.certified .bit false).certifiedStructure
  | .immediateSelection => Modules.Mux.certifiedStructure (.vector 32 .bit)
  | .addSubSummarySelection | .compareSelection => Modules.Mux.certifiedStructure .bit
  | .resetMatchOutputs => resetMatchSplitter.certified.certifiedStructure
  | .retainedMatchOutputs => retainedMatchSplitter.certified.certifiedStructure
  | .ordinarySummaryOutputs => ordinarySummarySplitter.certified.certifiedStructure
  | .falseValue => (Modules.Constant.certified .bit false).certifiedStructure

end Silean.Examples.PicoRV.Decoder.ResolveStage
