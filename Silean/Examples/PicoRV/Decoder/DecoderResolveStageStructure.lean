import Silean.Examples.PicoRV.Decoder.DecoderResolveStage
import Silean.Examples.PicoRV.Decoder.DecoderInstructionMatchStructure
import Silean.Examples.PicoRV.Decoder.DecoderImmediate
import Silean.Examples.PicoRV.Decoder.DecoderInstructionSummaryStructure
import Silean.Authoring.ModuleDesign
import Silean.Modules.EnabledRegister.EnabledRegister
import Silean.Modules.EnabledResetRegister.EnabledResetRegister
import Silean.Modules.Register.Register
import Silean.Modules.ResetRegister.ResetRegister
import Silean.Modules.Mux.Mux
import Silean.Modules.Constant.Constant
import Silean.Primitives.Not
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming

namespace Silean.Examples.PicoRV.Decoder.ResolveStage

open Silean
open Silean.Authoring
open Silean.Examples.PicoRV.Decoder

/-! ## Structural implementation

The 45 logical contract registers are grouped into six aggregate storage
instances. This grouping is structural only; the public contract retains the
source Verilog's individual state names and update behavior.

Instruction matching, immediate decoding, and instruction summaries are all
concrete children. This parent composes them through their public cycle
contracts. -/

def resetMatchRegister (index : Fin 23) : Register :=
  match index.val with
  | 0 => .instr_beq | 1 => .instr_bne | 2 => .instr_blt | 3 => .instr_bge
  | 4 => .instr_bltu | 5 => .instr_bgeu | 6 => .instr_addi | 7 => .instr_slti
  | 8 => .instr_sltiu | 9 => .instr_xori | 10 => .instr_ori | 11 => .instr_andi
  | 12 => .instr_add | 13 => .instr_sub | 14 => .instr_sll | 15 => .instr_slt
  | 16 => .instr_sltu | 17 => .instr_xor | 18 => .instr_srl | 19 => .instr_sra
  | 20 => .instr_or | 21 => .instr_and | _ => .instr_fence

def retainedMatchRegister (index : Fin 15) : Register :=
  match index.val with
  | 0 => .instr_lb | 1 => .instr_lh | 2 => .instr_lw | 3 => .instr_lbu
  | 4 => .instr_lhu | 5 => .instr_sb | 6 => .instr_sh | 7 => .instr_sw
  | 8 => .instr_slli | 9 => .instr_srli | 10 => .instr_srai
  | 11 => .instr_ecall_ebreak | 12 => .is_slli_srli_srai
  | 13 => .is_jalr_addi_slti_sltiu_xori_ori_andi | _ => .is_sll_srl_sra

def ordinarySummaryRegister (index : Fin 4) : Register :=
  match index.val with
  | 0 => .is_lui_auipc_jal | 1 => .is_slti_blt_slt
  | 2 => .is_sltiu_bltu_sltu | _ => .is_lbu_lhu_lw

def matchOutput : Register → InstructionMatch.Output
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

def summaryOutput : Register → InstructionSummary.Output
  | .is_lui_auipc_jal => .is_lui_auipc_jal
  | .is_lui_auipc_jal_jalr_addi_add_sub => .is_lui_auipc_jal_jalr_addi_add_sub
  | .is_slti_blt_slt => .is_slti_blt_slt
  | .is_sltiu_bltu_sltu => .is_sltiu_bltu_sltu
  | .is_lbu_lhu_lw => .is_lbu_lhu_lw
  | .is_compare => .is_compare
  | _ => .instr_trap -- unreachable for summary registers

def resetMatchType : SignalType := .vector 23 .bit
def retainedMatchType : SignalType := .vector 15 .bit
def ordinarySummaryType : SignalType := .vector 4 .bit
def immediateType : SignalType := .vector 32 .bit

def falseResetMatches : resetMatchType.Denote := fun _ => false

def resetMatchCombiner : Composition.SignalCombiner := .vector 23 .bit
def retainedMatchCombiner : Composition.SignalCombiner := .vector 15 .bit
def ordinarySummaryCombiner : Composition.SignalCombiner := .vector 4 .bit
def resetMatchSplitter : Composition.SignalSplitter := .vector 23 .bit
def retainedMatchSplitter : Composition.SignalSplitter := .vector 15 .bit
def ordinarySummarySplitter : Composition.SignalSplitter := .vector 4 .bit
end Silean.Examples.PicoRV.Decoder.ResolveStage

namespace Silean.Examples.PicoRV.Decoder

open Silean
open Silean.Authoring

module_design ResolveStage where
  boundary (ResolveStage.ports) (naming := ResolveStage.Naming.ports)
  instances {
    pseudoInverter := Primitives.notDesign,
    triggerEnable := Primitives.andDesign,
    resetInverter := Primitives.notDesign,
    instructionMatch := InstructionMatch.Structure.design,
    immediate := Immediate.design,
    instructionSummary := InstructionSummary.Structure.design,
    resetMatchNext := Naming.SignalAdapter.combinerDesign (.vector 23 .bit),
    retainedMatchNext := Naming.SignalAdapter.combinerDesign (.vector 15 .bit),
    ordinarySummaryNext := Naming.SignalAdapter.combinerDesign (.vector 4 .bit),
    resetMatchStorage := Modules.EnabledResetRegister.design
      ResolveStage.resetMatchType ResolveStage.falseResetMatches,
    retainedMatchStorage := Modules.EnabledRegister.design ResolveStage.retainedMatchType,
    immediateStorage := Modules.EnabledRegister.design ResolveStage.immediateType,
    ordinarySummaryStorage := Modules.Register.design ResolveStage.ordinarySummaryType,
    addSubSummaryStorage := Modules.Register.design .bit,
    compareStorage := Modules.ResetRegister.design .bit false,
    immediateSelection := Modules.Mux.design ResolveStage.immediateType,
    addSubSummarySelection := Modules.Mux.design .bit,
    compareSelection := Modules.Mux.design .bit,
    resetMatchOutputs := Naming.SignalAdapter.splitterDesign (.vector 23 .bit),
    retainedMatchOutputs := Naming.SignalAdapter.splitterDesign (.vector 15 .bit),
    ordinarySummaryOutputs := Naming.SignalAdapter.splitterDesign (.vector 4 .bit),
    falseValue := Modules.Constant.design .bit false }
  wiring {
  outputs {
    .instr_trap := instructionSummary.instr_trap,
    .instr_beq := resetMatchOutputs[0],
    .instr_bne := resetMatchOutputs[1],
    .instr_blt := resetMatchOutputs[2],
    .instr_bge := resetMatchOutputs[3],
    .instr_bltu := resetMatchOutputs[4],
    .instr_bgeu := resetMatchOutputs[5],
    .instr_lb := retainedMatchOutputs[0],
    .instr_lh := retainedMatchOutputs[1],
    .instr_lw := retainedMatchOutputs[2],
    .instr_lbu := retainedMatchOutputs[3],
    .instr_lhu := retainedMatchOutputs[4],
    .instr_sb := retainedMatchOutputs[5],
    .instr_sh := retainedMatchOutputs[6],
    .instr_sw := retainedMatchOutputs[7],
    .instr_addi := resetMatchOutputs[6],
    .instr_slti := resetMatchOutputs[7],
    .instr_sltiu := resetMatchOutputs[8],
    .instr_xori := resetMatchOutputs[9],
    .instr_ori := resetMatchOutputs[10],
    .instr_andi := resetMatchOutputs[11],
    .instr_slli := retainedMatchOutputs[8],
    .instr_srli := retainedMatchOutputs[9],
    .instr_srai := retainedMatchOutputs[10],
    .instr_add := resetMatchOutputs[12],
    .instr_sub := resetMatchOutputs[13],
    .instr_sll := resetMatchOutputs[14],
    .instr_slt := resetMatchOutputs[15],
    .instr_sltu := resetMatchOutputs[16],
    .instr_xor := resetMatchOutputs[17],
    .instr_srl := resetMatchOutputs[18],
    .instr_sra := resetMatchOutputs[19],
    .instr_or := resetMatchOutputs[20],
    .instr_and := resetMatchOutputs[21],
    .instr_fence := resetMatchOutputs[22],
    .decoded_imm := immediateStorage.q,
    .is_lui_auipc_jal := ordinarySummaryOutputs[0],
    .is_slli_srli_srai := retainedMatchOutputs[12],
    .is_jalr_addi_slti_sltiu_xori_ori_andi := retainedMatchOutputs[13],
    .is_sll_srl_sra := retainedMatchOutputs[14],
    .is_lui_auipc_jal_jalr_addi_add_sub := addSubSummaryStorage.output,
    .is_slti_blt_slt := ordinarySummaryOutputs[1],
    .is_sltiu_bltu_sltu := ordinarySummaryOutputs[2],
    .is_lbu_lhu_lw := ordinarySummaryOutputs[3],
    .is_compare := compareStorage.value }
  instance (.pseudoInverter) {
    .input := input.decoder_pseudo_trigger }
  instance (.triggerEnable) {
    .left := input.decoder_trigger,
    .right := pseudoInverter.output }
  instance (.resetInverter) {
    .input := input.resetn }
  instance (.instructionMatch) {
    .word := input.mem_rdata_q,
    .instr_jalr := input.instr_jalr,
    .is_beq_bne_blt_bge_bltu_bgeu := input.is_beq_bne_blt_bge_bltu_bgeu,
    .is_lb_lh_lw_lbu_lhu := input.is_lb_lh_lw_lbu_lhu,
    .is_sb_sh_sw := input.is_sb_sh_sw,
    .is_alu_reg_imm := input.is_alu_reg_imm,
    .is_alu_reg_reg := input.is_alu_reg_reg }
  instance (.immediate) {
    .word := input.mem_rdata_q,
    .decoded_imm_j := input.decoded_imm_j,
    .instr_jal := input.instr_jal,
    .instr_lui := input.instr_lui,
    .instr_auipc := input.instr_auipc,
    .instr_jalr := input.instr_jalr,
    .is_lb_lh_lw_lbu_lhu := input.is_lb_lh_lw_lbu_lhu,
    .is_alu_reg_imm := input.is_alu_reg_imm,
    .is_beq_bne_blt_bge_bltu_bgeu := input.is_beq_bne_blt_bge_bltu_bgeu,
    .is_sb_sh_sw := input.is_sb_sh_sw }
  instance (.instructionSummary) {
    .instr_lui := input.instr_lui,
    .instr_auipc := input.instr_auipc,
    .instr_jal := input.instr_jal,
    .instr_jalr := input.instr_jalr,
    .is_beq_bne_blt_bge_bltu_bgeu := input.is_beq_bne_blt_bge_bltu_bgeu,
    .instr_beq := resetMatchOutputs[0],
    .instr_bne := resetMatchOutputs[1],
    .instr_blt := resetMatchOutputs[2],
    .instr_bge := resetMatchOutputs[3],
    .instr_bltu := resetMatchOutputs[4],
    .instr_bgeu := resetMatchOutputs[5],
    .instr_lb := retainedMatchOutputs[0],
    .instr_lh := retainedMatchOutputs[1],
    .instr_lw := retainedMatchOutputs[2],
    .instr_lbu := retainedMatchOutputs[3],
    .instr_lhu := retainedMatchOutputs[4],
    .instr_sb := retainedMatchOutputs[5],
    .instr_sh := retainedMatchOutputs[6],
    .instr_sw := retainedMatchOutputs[7],
    .instr_addi := resetMatchOutputs[6],
    .instr_slti := resetMatchOutputs[7],
    .instr_sltiu := resetMatchOutputs[8],
    .instr_xori := resetMatchOutputs[9],
    .instr_ori := resetMatchOutputs[10],
    .instr_andi := resetMatchOutputs[11],
    .instr_slli := retainedMatchOutputs[8],
    .instr_srli := retainedMatchOutputs[9],
    .instr_srai := retainedMatchOutputs[10],
    .instr_add := resetMatchOutputs[12],
    .instr_sub := resetMatchOutputs[13],
    .instr_sll := resetMatchOutputs[14],
    .instr_slt := resetMatchOutputs[15],
    .instr_sltu := resetMatchOutputs[16],
    .instr_xor := resetMatchOutputs[17],
    .instr_srl := resetMatchOutputs[18],
    .instr_sra := resetMatchOutputs[19],
    .instr_or := resetMatchOutputs[20],
    .instr_and := resetMatchOutputs[21],
    .instr_ecall_ebreak := retainedMatchOutputs[11],
    .instr_fence := resetMatchOutputs[22] }
  instance (.resetMatchNext) {
    index := from (SignalSource.castType
      (InstructionMatch.output_signalType _)
      (c.instanceOutput .instructionMatch
        (ResolveStage.matchOutput (ResolveStage.resetMatchRegister index)))) }
  instance (.retainedMatchNext) {
    index := from (SignalSource.castType
      (InstructionMatch.output_signalType _)
      (c.instanceOutput .instructionMatch
        (ResolveStage.matchOutput (ResolveStage.retainedMatchRegister index)))) }
  instance (.ordinarySummaryNext) {
    index := from (SignalSource.castType
      (InstructionSummary.output_signalType _)
      (c.instanceOutput .instructionSummary
        (ResolveStage.summaryOutput (ResolveStage.ordinarySummaryRegister index)))) }
  instance (.resetMatchStorage) {
    .value := resetMatchNext.value,
    .enable := triggerEnable.output,
    .reset := resetInverter.output }
  instance (.retainedMatchStorage) {
    .data := retainedMatchNext.value,
    .enable := triggerEnable.output }
  instance (.immediateSelection) {
    .select := immediate.valid,
    .whenFalse := immediateStorage.q,
    .whenTrue := immediate.value }
  instance (.immediateStorage) {
    .data := immediateSelection.result,
    .enable := triggerEnable.output }
  instance (.ordinarySummaryStorage) {
    .input := ordinarySummaryNext.value }
  instance (.addSubSummarySelection) {
    .select := triggerEnable.output,
    .whenFalse := instructionSummary.is_lui_auipc_jal_jalr_addi_add_sub,
    .whenTrue := falseValue.output }
  instance (.addSubSummaryStorage) {
    .input := addSubSummarySelection.result }
  instance (.compareSelection) {
    .select := triggerEnable.output,
    .whenFalse := instructionSummary.is_compare,
    .whenTrue := falseValue.output }
  instance (.compareStorage) {
    .value := compareSelection.result,
    .reset := resetInverter.output }
  instance (.resetMatchOutputs) {
    .value := resetMatchStorage.value }
  instance (.retainedMatchOutputs) {
    .value := retainedMatchStorage.q }
  instance (.ordinarySummaryOutputs) {
    .value := ordinarySummaryStorage.output }
  instance (.falseValue) {}
  }

end Silean.Examples.PicoRV.Decoder

namespace Silean.Examples.PicoRV.Decoder.ResolveStage

open Silean

/-- The values exposed at the resolve-stage boundary, separated from the
mechanical `SignalSource` representation used by `wiring`. -/
def boundaryValues
    (childOutputs : (child : Instance) → (instancePorts.ports child).outputs.Values) :
    outputMap.Values
  | .instr_trap => childOutputs .instructionSummary .instr_trap
  | .instr_beq => childOutputs .resetMatchOutputs 0
  | .instr_bne => childOutputs .resetMatchOutputs 1
  | .instr_blt => childOutputs .resetMatchOutputs 2
  | .instr_bge => childOutputs .resetMatchOutputs 3
  | .instr_bltu => childOutputs .resetMatchOutputs 4
  | .instr_bgeu => childOutputs .resetMatchOutputs 5
  | .instr_lb => childOutputs .retainedMatchOutputs 0
  | .instr_lh => childOutputs .retainedMatchOutputs 1
  | .instr_lw => childOutputs .retainedMatchOutputs 2
  | .instr_lbu => childOutputs .retainedMatchOutputs 3
  | .instr_lhu => childOutputs .retainedMatchOutputs 4
  | .instr_sb => childOutputs .retainedMatchOutputs 5
  | .instr_sh => childOutputs .retainedMatchOutputs 6
  | .instr_sw => childOutputs .retainedMatchOutputs 7
  | .instr_addi => childOutputs .resetMatchOutputs 6
  | .instr_slti => childOutputs .resetMatchOutputs 7
  | .instr_sltiu => childOutputs .resetMatchOutputs 8
  | .instr_xori => childOutputs .resetMatchOutputs 9
  | .instr_ori => childOutputs .resetMatchOutputs 10
  | .instr_andi => childOutputs .resetMatchOutputs 11
  | .instr_slli => childOutputs .retainedMatchOutputs 8
  | .instr_srli => childOutputs .retainedMatchOutputs 9
  | .instr_srai => childOutputs .retainedMatchOutputs 10
  | .instr_add => childOutputs .resetMatchOutputs 12
  | .instr_sub => childOutputs .resetMatchOutputs 13
  | .instr_sll => childOutputs .resetMatchOutputs 14
  | .instr_slt => childOutputs .resetMatchOutputs 15
  | .instr_sltu => childOutputs .resetMatchOutputs 16
  | .instr_xor => childOutputs .resetMatchOutputs 17
  | .instr_srl => childOutputs .resetMatchOutputs 18
  | .instr_sra => childOutputs .resetMatchOutputs 19
  | .instr_or => childOutputs .resetMatchOutputs 20
  | .instr_and => childOutputs .resetMatchOutputs 21
  | .instr_fence => childOutputs .resetMatchOutputs 22
  | .decoded_imm => childOutputs .immediateStorage .q
  | .is_lui_auipc_jal => childOutputs .ordinarySummaryOutputs 0
  | .is_slli_srli_srai => childOutputs .retainedMatchOutputs 12
  | .is_jalr_addi_slti_sltiu_xori_ori_andi => childOutputs .retainedMatchOutputs 13
  | .is_sll_srl_sra => childOutputs .retainedMatchOutputs 14
  | .is_lui_auipc_jal_jalr_addi_add_sub => childOutputs .addSubSummaryStorage .output
  | .is_slti_blt_slt => childOutputs .ordinarySummaryOutputs 1
  | .is_sltiu_bltu_sltu => childOutputs .ordinarySummaryOutputs 2
  | .is_lbu_lhu_lw => childOutputs .ordinarySummaryOutputs 3
  | .is_compare => childOutputs .compareStorage .value

@[simp] theorem moduleOutput_value
    (inputs : inputMap.Values)
    (childOutputs : (child : Instance) → (instancePorts.ports child).outputs.Values)
    (output : Output) :
    (wiring.moduleOutput output).value inputs childOutputs =
      boundaryValues childOutputs output := by
  cases output <;> rfl

/-- The instruction-summary child's inputs, in ordinary values rather than
the `SignalSource` form used by the authored wiring. -/
def instructionSummaryInputs (inputs : inputMap.Values)
    (childOutputs : (child : Instance) → (instancePorts.ports child).outputs.Values) :
    InstructionSummary.inputMap.Values
  | .instr_lui => inputs .instr_lui
  | .instr_auipc => inputs .instr_auipc
  | .instr_jal => inputs .instr_jal
  | .instr_jalr => inputs .instr_jalr
  | .is_beq_bne_blt_bge_bltu_bgeu => inputs .is_beq_bne_blt_bge_bltu_bgeu
  | .instr_beq => childOutputs .resetMatchOutputs 0
  | .instr_bne => childOutputs .resetMatchOutputs 1
  | .instr_blt => childOutputs .resetMatchOutputs 2
  | .instr_bge => childOutputs .resetMatchOutputs 3
  | .instr_bltu => childOutputs .resetMatchOutputs 4
  | .instr_bgeu => childOutputs .resetMatchOutputs 5
  | .instr_lb => childOutputs .retainedMatchOutputs 0
  | .instr_lh => childOutputs .retainedMatchOutputs 1
  | .instr_lw => childOutputs .retainedMatchOutputs 2
  | .instr_lbu => childOutputs .retainedMatchOutputs 3
  | .instr_lhu => childOutputs .retainedMatchOutputs 4
  | .instr_sb => childOutputs .retainedMatchOutputs 5
  | .instr_sh => childOutputs .retainedMatchOutputs 6
  | .instr_sw => childOutputs .retainedMatchOutputs 7
  | .instr_addi => childOutputs .resetMatchOutputs 6
  | .instr_slti => childOutputs .resetMatchOutputs 7
  | .instr_sltiu => childOutputs .resetMatchOutputs 8
  | .instr_xori => childOutputs .resetMatchOutputs 9
  | .instr_ori => childOutputs .resetMatchOutputs 10
  | .instr_andi => childOutputs .resetMatchOutputs 11
  | .instr_slli => childOutputs .retainedMatchOutputs 8
  | .instr_srli => childOutputs .retainedMatchOutputs 9
  | .instr_srai => childOutputs .retainedMatchOutputs 10
  | .instr_add => childOutputs .resetMatchOutputs 12
  | .instr_sub => childOutputs .resetMatchOutputs 13
  | .instr_sll => childOutputs .resetMatchOutputs 14
  | .instr_slt => childOutputs .resetMatchOutputs 15
  | .instr_sltu => childOutputs .resetMatchOutputs 16
  | .instr_xor => childOutputs .resetMatchOutputs 17
  | .instr_srl => childOutputs .resetMatchOutputs 18
  | .instr_sra => childOutputs .resetMatchOutputs 19
  | .instr_or => childOutputs .resetMatchOutputs 20
  | .instr_and => childOutputs .resetMatchOutputs 21
  | .instr_ecall_ebreak => childOutputs .retainedMatchOutputs 11
  | .instr_fence => childOutputs .resetMatchOutputs 22

@[simp] theorem instructionSummaryInput_value
    (inputs : inputMap.Values)
    (childOutputs : (child : Instance) → (instancePorts.ports child).outputs.Values)
    (input : InstructionSummary.Input) :
    (wiring.instanceInput .instructionSummary input).value inputs childOutputs =
      instructionSummaryInputs inputs childOutputs input := by
  cases input <;> rfl

end Silean.Examples.PicoRV.Decoder.ResolveStage
