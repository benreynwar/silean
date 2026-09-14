import Silean.Examples.PicoRV.Decoder.DecoderInstructionMatch
import Silean.Examples.PicoRV.Decoder.DecoderInstructionFields
import Silean.Examples.PicoRV.Decoder.DecoderInstructionMatchGate
import Silean.Authoring.ModuleDesign
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.Or

namespace Silean.Examples.PicoRV.Decoder.InstructionMatch

open Silean
open Silean.Authoring

/-! The structural matcher shares field decoders just as the source Verilog
shares its `funct3` and `funct7` wires. Each exact instruction flag is produced
by a `MatchGate` child from the broad opcode-class enable, field comparison,
and optional qualifier. ECALL/EBREAK and FENCE use comparisons of
exactly the source bits named by their predicates. The final three outputs are
OR reductions of the already decoded instruction flags. -/

inductive Exact
  | instr_beq | instr_bne | instr_blt | instr_bge | instr_bltu | instr_bgeu
  | instr_lb | instr_lh | instr_lw | instr_lbu | instr_lhu
  | instr_sb | instr_sh | instr_sw
  | instr_addi | instr_slti | instr_sltiu | instr_xori | instr_ori | instr_andi
  | instr_slli | instr_srli | instr_srai
  | instr_add | instr_sub | instr_sll | instr_slt | instr_sltu
  | instr_xor | instr_srl | instr_sra | instr_or | instr_and
  | instr_ecall_ebreak | instr_fence
deriving DecidableEq, Enumeration

def Exact.output : Exact → Output
  | .instr_beq => .instr_beq | .instr_bne => .instr_bne
  | .instr_blt => .instr_blt | .instr_bge => .instr_bge
  | .instr_bltu => .instr_bltu | .instr_bgeu => .instr_bgeu
  | .instr_lb => .instr_lb | .instr_lh => .instr_lh | .instr_lw => .instr_lw
  | .instr_lbu => .instr_lbu | .instr_lhu => .instr_lhu
  | .instr_sb => .instr_sb | .instr_sh => .instr_sh | .instr_sw => .instr_sw
  | .instr_addi => .instr_addi | .instr_slti => .instr_slti
  | .instr_sltiu => .instr_sltiu | .instr_xori => .instr_xori
  | .instr_ori => .instr_ori | .instr_andi => .instr_andi
  | .instr_slli => .instr_slli | .instr_srli => .instr_srli
  | .instr_srai => .instr_srai | .instr_add => .instr_add
  | .instr_sub => .instr_sub | .instr_sll => .instr_sll
  | .instr_slt => .instr_slt | .instr_sltu => .instr_sltu
  | .instr_xor => .instr_xor | .instr_srl => .instr_srl
  | .instr_sra => .instr_sra | .instr_or => .instr_or | .instr_and => .instr_and
  | .instr_ecall_ebreak => .instr_ecall_ebreak | .instr_fence => .instr_fence

def Exact.name (exact : Exact) : String :=
  s!"match_{((inferInstance : Enumeration Exact).locate exact).toFin.val}"

def exactFunct3 : Exact → Fin 8
  | .instr_beq | .instr_lb | .instr_sb | .instr_addi | .instr_add | .instr_sub => 0
  | .instr_bne | .instr_lh | .instr_sh | .instr_slli | .instr_sll => 1
  | .instr_lw | .instr_sw | .instr_slti | .instr_slt => 2
  | .instr_sltiu | .instr_sltu => 3
  | .instr_blt | .instr_lbu | .instr_xori | .instr_xor => 4
  | .instr_bge | .instr_lhu | .instr_srli | .instr_srai | .instr_srl | .instr_sra => 5
  | .instr_bltu | .instr_ori | .instr_or => 6
  | .instr_bgeu | .instr_andi | .instr_and => 7
  | .instr_ecall_ebreak | .instr_fence => 0

def Exact.needsFunct7Zero : Exact → Bool
  | .instr_slli | .instr_srli | .instr_add | .instr_sll | .instr_slt
  | .instr_sltu | .instr_xor | .instr_srl | .instr_or | .instr_and => true
  | _ => false

def Exact.needsFunct7Alternate : Exact → Bool
  | .instr_srai | .instr_sub | .instr_sra => true
  | _ => false

def broadValue (inputs : Inputs) : Exact → Bool
  | .instr_beq | .instr_bne | .instr_blt | .instr_bge
  | .instr_bltu | .instr_bgeu => inputs.is_beq_bne_blt_bge_bltu_bgeu
  | .instr_lb | .instr_lh | .instr_lw | .instr_lbu | .instr_lhu =>
      inputs.is_lb_lh_lw_lbu_lhu
  | .instr_sb | .instr_sh | .instr_sw => inputs.is_sb_sh_sw
  | .instr_addi | .instr_slti | .instr_sltiu | .instr_xori | .instr_ori
  | .instr_andi | .instr_slli | .instr_srli | .instr_srai => inputs.is_alu_reg_imm
  | .instr_add | .instr_sub | .instr_sll | .instr_slt | .instr_sltu
  | .instr_xor | .instr_srl | .instr_sra | .instr_or | .instr_and =>
      inputs.is_alu_reg_reg
  | .instr_ecall_ebreak => decide (opcode inputs.word = 0x73)
  | .instr_fence => decide (opcode inputs.word = 0x0f)

def fieldValue (inputs : Inputs) : Exact → Bool
  | .instr_ecall_ebreak => decide (field inputs.word 21 11 = 0)
  | exact => decide (funct3 inputs.word = (exactFunct3 exact).val)

def qualifierValue (inputs : Inputs) (exact : Exact) : Bool :=
  if exact = .instr_ecall_ebreak then decide (field inputs.word 7 13 = 0)
  else if exact.needsFunct7Zero then decide (funct7 inputs.word = 0)
  else if exact.needsFunct7Alternate then decide (funct7 inputs.word = 0x20)
  else true

def structuralExactValue (inputs : Inputs) (exact : Exact) : Bool :=
  (broadValue inputs exact && fieldValue inputs exact) && qualifierValue inputs exact

def exactValue (inputs : Inputs) : Exact → Bool
  | .instr_beq => outputValues inputs .instr_beq
  | .instr_bne => outputValues inputs .instr_bne
  | .instr_blt => outputValues inputs .instr_blt
  | .instr_bge => outputValues inputs .instr_bge
  | .instr_bltu => outputValues inputs .instr_bltu
  | .instr_bgeu => outputValues inputs .instr_bgeu
  | .instr_lb => outputValues inputs .instr_lb
  | .instr_lh => outputValues inputs .instr_lh
  | .instr_lw => outputValues inputs .instr_lw
  | .instr_lbu => outputValues inputs .instr_lbu
  | .instr_lhu => outputValues inputs .instr_lhu
  | .instr_sb => outputValues inputs .instr_sb
  | .instr_sh => outputValues inputs .instr_sh
  | .instr_sw => outputValues inputs .instr_sw
  | .instr_addi => outputValues inputs .instr_addi
  | .instr_slti => outputValues inputs .instr_slti
  | .instr_sltiu => outputValues inputs .instr_sltiu
  | .instr_xori => outputValues inputs .instr_xori
  | .instr_ori => outputValues inputs .instr_ori
  | .instr_andi => outputValues inputs .instr_andi
  | .instr_slli => outputValues inputs .instr_slli
  | .instr_srli => outputValues inputs .instr_srli
  | .instr_srai => outputValues inputs .instr_srai
  | .instr_add => outputValues inputs .instr_add
  | .instr_sub => outputValues inputs .instr_sub
  | .instr_sll => outputValues inputs .instr_sll
  | .instr_slt => outputValues inputs .instr_slt
  | .instr_sltu => outputValues inputs .instr_sltu
  | .instr_xor => outputValues inputs .instr_xor
  | .instr_srl => outputValues inputs .instr_srl
  | .instr_sra => outputValues inputs .instr_sra
  | .instr_or => outputValues inputs .instr_or
  | .instr_and => outputValues inputs .instr_and
  | .instr_ecall_ebreak => outputValues inputs .instr_ecall_ebreak
  | .instr_fence => outputValues inputs .instr_fence

theorem structuralExactValue_eq (inputs : Inputs) (exact : Exact) :
    structuralExactValue inputs exact = exactValue inputs exact := by
  cases exact <;>
    simp [structuralExactValue, broadValue, fieldValue, qualifierValue,
      Exact.needsFunct7Zero, Exact.needsFunct7Alternate, exactFunct3,
      exactValue, outputValues, matches3, matches37,
      Bool.and_assoc] <;> rfl

module_design Structure (name := "PicoRVDecoderInstructionMatch") where
  boundary (ports) (naming := Naming.ports)
  instances {
    fields := InstructionFields.Structure.design,
    exactMatch (exact : Exact in (inferInstance : Enumeration Exact))
      (name := Exact.name exact) := MatchGate.Structure.design,
    immediateShift01 := Primitives.orDesign,
    immediateShiftGroup := Primitives.orDesign,
    arithmetic01 := Primitives.orDesign,
    arithmetic23 := Primitives.orDesign,
    arithmetic45 := Primitives.orDesign,
    arithmetic0123 := Primitives.orDesign,
    arithmetic012345 := Primitives.orDesign,
    immediateArithmeticGroup := Primitives.orDesign,
    registerShift01 := Primitives.orDesign,
    registerShiftGroup := Primitives.orDesign }
  wiring {
  outputs {
    .instr_beq := exactMatch(.instr_beq)[.result],
    .instr_bne := exactMatch(.instr_bne)[.result],
    .instr_blt := exactMatch(.instr_blt)[.result],
    .instr_bge := exactMatch(.instr_bge)[.result],
    .instr_bltu := exactMatch(.instr_bltu)[.result],
    .instr_bgeu := exactMatch(.instr_bgeu)[.result],
    .instr_lb := exactMatch(.instr_lb)[.result],
    .instr_lh := exactMatch(.instr_lh)[.result],
    .instr_lw := exactMatch(.instr_lw)[.result],
    .instr_lbu := exactMatch(.instr_lbu)[.result],
    .instr_lhu := exactMatch(.instr_lhu)[.result],
    .instr_sb := exactMatch(.instr_sb)[.result],
    .instr_sh := exactMatch(.instr_sh)[.result],
    .instr_sw := exactMatch(.instr_sw)[.result],
    .instr_addi := exactMatch(.instr_addi)[.result],
    .instr_slti := exactMatch(.instr_slti)[.result],
    .instr_sltiu := exactMatch(.instr_sltiu)[.result],
    .instr_xori := exactMatch(.instr_xori)[.result],
    .instr_ori := exactMatch(.instr_ori)[.result],
    .instr_andi := exactMatch(.instr_andi)[.result],
    .instr_slli := exactMatch(.instr_slli)[.result],
    .instr_srli := exactMatch(.instr_srli)[.result],
    .instr_srai := exactMatch(.instr_srai)[.result],
    .instr_add := exactMatch(.instr_add)[.result],
    .instr_sub := exactMatch(.instr_sub)[.result],
    .instr_sll := exactMatch(.instr_sll)[.result],
    .instr_slt := exactMatch(.instr_slt)[.result],
    .instr_sltu := exactMatch(.instr_sltu)[.result],
    .instr_xor := exactMatch(.instr_xor)[.result],
    .instr_srl := exactMatch(.instr_srl)[.result],
    .instr_sra := exactMatch(.instr_sra)[.result],
    .instr_or := exactMatch(.instr_or)[.result],
    .instr_and := exactMatch(.instr_and)[.result],
    .instr_ecall_ebreak := exactMatch(.instr_ecall_ebreak)[.result],
    .instr_fence := exactMatch(.instr_fence)[.result],
    .is_slli_srli_srai := immediateShiftGroup.output,
    .is_jalr_addi_slti_sltiu_xori_ori_andi := immediateArithmeticGroup.output,
    .is_sll_srl_sra := registerShiftGroup.output }
  instance (.fields) { .word := input.word }
  instance (.exactMatch exact) {
    .broad := from (match exact with
      | .instr_beq | .instr_bne | .instr_blt | .instr_bge
      | .instr_bltu | .instr_bgeu => c.moduleInput .is_beq_bne_blt_bge_bltu_bgeu
      | .instr_lb | .instr_lh | .instr_lw | .instr_lbu | .instr_lhu =>
          c.moduleInput .is_lb_lh_lw_lbu_lhu
      | .instr_sb | .instr_sh | .instr_sw => c.moduleInput .is_sb_sh_sw
      | .instr_addi | .instr_slti | .instr_sltiu | .instr_xori | .instr_ori
      | .instr_andi | .instr_slli | .instr_srli | .instr_srai =>
          c.moduleInput .is_alu_reg_imm
      | .instr_add | .instr_sub | .instr_sll | .instr_slt | .instr_sltu
      | .instr_xor | .instr_srl | .instr_sra | .instr_or | .instr_and =>
          c.moduleInput .is_alu_reg_reg
      | .instr_ecall_ebreak => c.instanceOutput .fields .opcode_system
      | .instr_fence => c.instanceOutput .fields .opcode_fence),
    .field := from (match exact with
      | .instr_ecall_ebreak => c.instanceOutput .fields .system_middle_zero
      | .instr_fence => c.instanceOutput .fields .funct3_0
      | .instr_beq | .instr_lb | .instr_sb | .instr_addi | .instr_add
      | .instr_sub => c.instanceOutput .fields .funct3_0
      | .instr_bne | .instr_lh | .instr_sh | .instr_slli
      | .instr_sll => c.instanceOutput .fields .funct3_1
      | .instr_lw | .instr_sw | .instr_slti
      | .instr_slt => c.instanceOutput .fields .funct3_2
      | .instr_sltiu | .instr_sltu => c.instanceOutput .fields .funct3_3
      | .instr_blt | .instr_lbu | .instr_xori
      | .instr_xor => c.instanceOutput .fields .funct3_4
      | .instr_bge | .instr_lhu | .instr_srli | .instr_srai | .instr_srl
      | .instr_sra => c.instanceOutput .fields .funct3_5
      | .instr_bltu | .instr_ori | .instr_or => c.instanceOutput .fields .funct3_6
      | .instr_bgeu | .instr_andi | .instr_and =>
          c.instanceOutput .fields .funct3_7),
    .qualifier := from (if exact = .instr_ecall_ebreak then
        c.instanceOutput .fields .system_outer_zero
      else if exact.needsFunct7Zero then c.instanceOutput .fields .funct7_zero
      else if exact.needsFunct7Alternate then
        c.instanceOutput .fields .funct7_alternate
      else c.instanceOutput .fields .true_value) }
  instance (.immediateShift01) {
    .left := exactMatch(.instr_slli)[.result],
    .right := exactMatch(.instr_srli)[.result] }
  instance (.immediateShiftGroup) {
    .left := immediateShift01.output,
    .right := exactMatch(.instr_srai)[.result] }
  instance (.arithmetic01) {
    .left := input.instr_jalr,
    .right := exactMatch(.instr_addi)[.result] }
  instance (.arithmetic23) {
    .left := exactMatch(.instr_slti)[.result],
    .right := exactMatch(.instr_sltiu)[.result] }
  instance (.arithmetic45) {
    .left := exactMatch(.instr_xori)[.result],
    .right := exactMatch(.instr_ori)[.result] }
  instance (.arithmetic0123) {
    .left := arithmetic01.output,
    .right := arithmetic23.output }
  instance (.arithmetic012345) {
    .left := arithmetic0123.output,
    .right := arithmetic45.output }
  instance (.immediateArithmeticGroup) {
    .left := arithmetic012345.output,
    .right := exactMatch(.instr_andi)[.result] }
  instance (.registerShift01) {
    .left := exactMatch(.instr_sll)[.result],
    .right := exactMatch(.instr_srl)[.result] }
  instance (.registerShiftGroup) {
    .left := registerShift01.output,
    .right := exactMatch(.instr_sra)[.result] }
  }

end Silean.Examples.PicoRV.Decoder.InstructionMatch
