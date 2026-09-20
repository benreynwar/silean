import PicoRV.Decoder.DecoderTypes
import Silean.Authoring.ModuleDesign
import Silean.Authoring.SignalSchemaDeclaration
import Silean.Modules.Constant.Constant
import Silean.Modules.EnabledRegister.EnabledRegisterDerived
import Silean.Modules.EnabledResetRegister.EnabledResetRegisterDerived
import Silean.Modules.EqualsConstant.EqualsConstant
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Modules.VectorLayout.VectorLayout
import Silean.Modules.VectorSlice.VectorSlice
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.And
import Silean.Primitives.Not

/-! Expanded typed hierarchy for the registered decoder capture stage. -/

namespace PicoRV.Decoder.CaptureStage

open Silean
open Silean.Authoring
open PicoRV.Decoder

module_ports ports where
  input resetn : .bit,
  input mem_do_rinst : .bit,
  input mem_done : .bit,
  input mem_rdata_latched : .vector 32 .bit,
  output instr_lui : .bit,
  output instr_auipc : .bit,
  output instr_jal : .bit,
  output instr_jalr : .bit,
  output decoded_rd : .vector 5 .bit,
  output decoded_rs1 : .vector 5 .bit,
  output decoded_rs2 : .vector 5 .bit,
  output decoded_imm_j : .vector 32 .bit,
  output compressed_instr : .bit,
  output is_beq_bne_blt_bge_bltu_bgeu : .bit,
  output is_lb_lh_lw_lbu_lhu : .bit,
  output is_sb_sh_sw : .bit,
  output is_alu_reg_imm : .bit,
  output is_alu_reg_reg : .bit

@[reducible] def stateMap : SignalMap := outputMap

def bits (width value : Nat) : Fin width → Bool :=
  fun index => value.testBit index.val

def immediateJLayout (index : Fin 32) : Silean.Modules.VectorLayout.BitSource 32 :=
  if _zero : index.val = 0 then .constant false
  else if _low : index.val ≤ 10 then .input ⟨index.val + 20, by omega⟩
  else if _eleven : index.val = 11 then .input ⟨20, by omega⟩
  else if _middle : index.val ≤ 19 then .input index
  else .input ⟨31, by omega⟩

signal_schema Stored where
  instr_lui : Silean.Authoring.SignalSchema.bit,
  instr_auipc : Silean.Authoring.SignalSchema.bit,
  instr_jal : Silean.Authoring.SignalSchema.bit,
  instr_jalr : Silean.Authoring.SignalSchema.bit,
  decoded_rd : Silean.Authoring.SignalSchema.vector 5 Silean.Authoring.SignalSchema.bit,
  decoded_rs1 : Silean.Authoring.SignalSchema.vector 5 Silean.Authoring.SignalSchema.bit,
  decoded_rs2 : Silean.Authoring.SignalSchema.vector 5 Silean.Authoring.SignalSchema.bit,
  decoded_imm_j : Silean.Authoring.SignalSchema.vector 32 Silean.Authoring.SignalSchema.bit,
  compressed_instr : Silean.Authoring.SignalSchema.bit,
  is_lb_lh_lw_lbu_lhu : Silean.Authoring.SignalSchema.bit,
  is_sb_sh_sw : Silean.Authoring.SignalSchema.bit,
  is_alu_reg_imm : Silean.Authoring.SignalSchema.bit,
  is_alu_reg_reg : Silean.Authoring.SignalSchema.bit

abbrev StoredField := Stored.Field
@[reducible] def storedMap : SignalMap := Stored.signalMap
abbrev storedType : SignalType := Stored.signalType

end PicoRV.Decoder.CaptureStage

namespace PicoRV.Decoder

open Silean
open Silean.Authoring

module_design CaptureStage (name := "picorv32_decoder_capture") where
  boundary (CaptureStage.ports) (naming := CaptureStage.Naming.ports)
  instances {
    captureEnable (name := .indexed "and" 0) := Silean.Primitives.andDesign,
    reset (name := .indexed "not" 0) := Silean.Primitives.notDesign,
    opcode (name := .indexed "vector_slice" 0) :=
      Silean.Modules.VectorSlice.design .bit 0 7 25,
    funct3 (name := .indexed "vector_slice" 1) :=
      Silean.Modules.VectorSlice.design .bit 12 3 17,
    decodedRd (name := .indexed "vector_slice" 2) :=
      Silean.Modules.VectorSlice.design .bit 7 5 20,
    decodedRs1 (name := .indexed "vector_slice" 3) :=
      Silean.Modules.VectorSlice.design .bit 15 5 12,
    decodedRs2 (name := .indexed "vector_slice" 4) :=
      Silean.Modules.VectorSlice.design .bit 20 5 7,
    opcodeLui (name := .indexed "equals_constant" 0) :=
      Silean.Modules.EqualsConstant.design (.vector 7 .bit) (CaptureStage.bits 7 0x37),
    opcodeAuipc (name := .indexed "equals_constant" 1) :=
      Silean.Modules.EqualsConstant.design (.vector 7 .bit) (CaptureStage.bits 7 0x17),
    opcodeJal (name := .indexed "equals_constant" 2) :=
      Silean.Modules.EqualsConstant.design (.vector 7 .bit) (CaptureStage.bits 7 0x6f),
    opcodeJalr (name := .indexed "equals_constant" 3) :=
      Silean.Modules.EqualsConstant.design (.vector 7 .bit) (CaptureStage.bits 7 0x67),
    opcodeBranch (name := .indexed "equals_constant" 4) :=
      Silean.Modules.EqualsConstant.design (.vector 7 .bit) (CaptureStage.bits 7 0x63),
    opcodeLoad (name := .indexed "equals_constant" 5) :=
      Silean.Modules.EqualsConstant.design (.vector 7 .bit) (CaptureStage.bits 7 0x03),
    opcodeStore (name := .indexed "equals_constant" 6) :=
      Silean.Modules.EqualsConstant.design (.vector 7 .bit) (CaptureStage.bits 7 0x23),
    opcodeAluImm (name := .indexed "equals_constant" 7) :=
      Silean.Modules.EqualsConstant.design (.vector 7 .bit) (CaptureStage.bits 7 0x13),
    opcodeAluReg (name := .indexed "equals_constant" 8) :=
      Silean.Modules.EqualsConstant.design (.vector 7 .bit) (CaptureStage.bits 7 0x33),
    funct3Zero (name := .indexed "equals_constant" 9) :=
      Silean.Modules.EqualsConstant.design (.vector 3 .bit) (CaptureStage.bits 3 0),
    jalr (name := .indexed "and" 1) := Silean.Primitives.andDesign,
    zero (name := .indexed "constant" 0) := Silean.Modules.Constant.design .bit false,
    immediate (name := .indexed "vector_layout" 0) :=
      Silean.Modules.VectorLayout.design 32 32 CaptureStage.immediateJLayout,
    storedNext (name := .indexed "named_tuple_combiner" 0) :=
      Silean.Modules.NamedTupleCombiner.designWith
        CaptureStage.storedMap CaptureStage.Stored.schema,
    stored (name := .indexed "enabled_register" 0) :=
      Silean.Modules.EnabledRegister.designWith CaptureStage.storedType
        CaptureStage.Stored.schema,
    storedOutputs (name := .indexed "named_tuple_splitter" 0) :=
      Silean.Modules.NamedTupleSplitter.designWith
        CaptureStage.storedMap CaptureStage.Stored.schema,
    branch (name := .indexed "enabled_reset_register" 0) :=
      Silean.Modules.EnabledResetRegister.design .bit false }
  wiring {
    outputs {
      .instr_lui := storedOutputs[.instr_lui],
      .instr_auipc := storedOutputs[.instr_auipc],
      .instr_jal := storedOutputs[.instr_jal],
      .instr_jalr := storedOutputs[.instr_jalr],
      .decoded_rd := storedOutputs[.decoded_rd],
      .decoded_rs1 := storedOutputs[.decoded_rs1],
      .decoded_rs2 := storedOutputs[.decoded_rs2],
      .decoded_imm_j := storedOutputs[.decoded_imm_j],
      .compressed_instr := storedOutputs[.compressed_instr],
      .is_beq_bne_blt_bge_bltu_bgeu := branch.value,
      .is_lb_lh_lw_lbu_lhu := storedOutputs[.is_lb_lh_lw_lbu_lhu],
      .is_sb_sh_sw := storedOutputs[.is_sb_sh_sw],
      .is_alu_reg_imm := storedOutputs[.is_alu_reg_imm],
      .is_alu_reg_reg := storedOutputs[.is_alu_reg_reg] }
    instance (.captureEnable) { .left := input.mem_do_rinst, .right := input.mem_done }
    instance (.reset) { .input := input.resetn }
    instance (.opcode) { .value := input.mem_rdata_latched }
    instance (.funct3) { .value := input.mem_rdata_latched }
    instance (.decodedRd) { .value := input.mem_rdata_latched }
    instance (.decodedRs1) { .value := input.mem_rdata_latched }
    instance (.decodedRs2) { .value := input.mem_rdata_latched }
    instance (.opcodeLui) { .value := opcode.result }
    instance (.opcodeAuipc) { .value := opcode.result }
    instance (.opcodeJal) { .value := opcode.result }
    instance (.opcodeJalr) { .value := opcode.result }
    instance (.opcodeBranch) { .value := opcode.result }
    instance (.opcodeLoad) { .value := opcode.result }
    instance (.opcodeStore) { .value := opcode.result }
    instance (.opcodeAluImm) { .value := opcode.result }
    instance (.opcodeAluReg) { .value := opcode.result }
    instance (.funct3Zero) { .value := funct3.result }
    instance (.jalr) { .left := opcodeJalr.result, .right := funct3Zero.result }
    instance (.zero) {}
    instance (.immediate) { .input := input.mem_rdata_latched }
    instance (.storedNext) {
      .instr_lui := opcodeLui.result,
      .instr_auipc := opcodeAuipc.result,
      .instr_jal := opcodeJal.result,
      .instr_jalr := jalr.output,
      .decoded_rd := decodedRd.result,
      .decoded_rs1 := decodedRs1.result,
      .decoded_rs2 := decodedRs2.result,
      .decoded_imm_j := immediate.output,
      .compressed_instr := zero.output,
      .is_lb_lh_lw_lbu_lhu := opcodeLoad.result,
      .is_sb_sh_sw := opcodeStore.result,
      .is_alu_reg_imm := opcodeAluImm.result,
      .is_alu_reg_reg := opcodeAluReg.result }
    instance (.stored) { .data := storedNext.value, .enable := captureEnable.output }
    instance (.storedOutputs) { .value := stored.q }
    instance (.branch) {
      .value := opcodeBranch.result,
      .enable := captureEnable.output,
      .reset := reset.output }
  }

end PicoRV.Decoder
