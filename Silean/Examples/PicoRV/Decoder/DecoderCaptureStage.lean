import Silean.Examples.PicoRV.Decoder.DecoderTypes
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModuleDesign
import Silean.Authoring.ModulePorts
import Silean.Authoring.SignalSchemaDeclaration
import Silean.Modules.VectorSlice.VectorSlice
import Silean.Modules.EqualsConstant.EqualsConstant
import Silean.Modules.EnabledRegister.EnabledRegister
import Silean.Modules.EnabledResetRegister.EnabledResetRegister
import Silean.Modules.Constant.Constant
import Silean.Modules.VectorLayout.VectorLayout
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Naming.SignalAdapterNaming
import Silean.Naming.PrimitiveNaming

namespace Silean.Examples.PicoRV.Decoder.CaptureStage

open Silean
open Silean.Authoring
open Silean.Examples.PicoRV.Decoder

/-! The first registered decoder stage. It captures broad opcode classes,
register addresses, and the J immediate when an instruction read completes.
Only the branch-class register is reset in the selected PicoRV32 source. -/

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

/-- The capture stage exposes its entire current state as its outputs. -/
@[reducible] def stateMap : SignalMap := outputMap

def bits (width value : Nat) : Fin width → Bool :=
  fun index => value.testBit index.val

/-- PicoRV32's J-immediate bit layout. Bit zero is fixed low, bits 1–10 come
from instruction bits 21–30, bit 11 comes from bit 20, bits 12–19 are copied,
and bits 20–31 repeat the sign bit. -/
def immediateJLayout (index : Fin 32) : Modules.VectorLayout.BitSource 32 :=
  if _zero : index.val = 0 then .constant false
  else if _low : index.val ≤ 10 then .input ⟨index.val + 20, by omega⟩
  else if _eleven : index.val = 11 then .input ⟨20, by omega⟩
  else if _middle : index.val ≤ 19 then .input index
  else .input ⟨31, by omega⟩

/-! ## Hardware structure

The source's thirteen non-reset fields share one aggregate enabled register.
The branch-class flag uses a separate enabled/reset register because the final
reset block overrides only that assignment. -/

signal_schema Stored where
  instr_lui : SignalSchema.bit,
  instr_auipc : SignalSchema.bit,
  instr_jal : SignalSchema.bit,
  instr_jalr : SignalSchema.bit,
  decoded_rd : SignalSchema.vector 5 SignalSchema.bit,
  decoded_rs1 : SignalSchema.vector 5 SignalSchema.bit,
  decoded_rs2 : SignalSchema.vector 5 SignalSchema.bit,
  decoded_imm_j : SignalSchema.vector 32 SignalSchema.bit,
  compressed_instr : SignalSchema.bit,
  is_lb_lh_lw_lbu_lhu : SignalSchema.bit,
  is_sb_sh_sw : SignalSchema.bit,
  is_alu_reg_imm : SignalSchema.bit,
  is_alu_reg_reg : SignalSchema.bit

abbrev StoredField := Stored.Field

@[reducible] def storedMap : SignalMap :=
  Stored.signalMap

def storedType : SignalType := storedMap.tupleType

end Silean.Examples.PicoRV.Decoder.CaptureStage

namespace Silean.Examples.PicoRV.Decoder

open Silean
open Silean.Authoring

module_design CaptureStage (name := "picorv32_decoder_capture") where
  boundary (CaptureStage.ports) (naming := CaptureStage.Naming.ports)
  instances {
    captureEnable := Primitives.andDesign,
    reset := Primitives.notDesign,
    opcode := Modules.VectorSlice.design .bit 0 7 25,
    funct3 := Modules.VectorSlice.design .bit 12 3 17,
    decodedRd := Modules.VectorSlice.design .bit 7 5 20,
    decodedRs1 := Modules.VectorSlice.design .bit 15 5 12,
    decodedRs2 := Modules.VectorSlice.design .bit 20 5 7,
    opcodeLui := Modules.EqualsConstant.design
      (.vector 7 .bit) (CaptureStage.bits 7 0x37),
    opcodeAuipc := Modules.EqualsConstant.design
      (.vector 7 .bit) (CaptureStage.bits 7 0x17),
    opcodeJal := Modules.EqualsConstant.design
      (.vector 7 .bit) (CaptureStage.bits 7 0x6f),
    opcodeJalr := Modules.EqualsConstant.design
      (.vector 7 .bit) (CaptureStage.bits 7 0x67),
    opcodeBranch := Modules.EqualsConstant.design
      (.vector 7 .bit) (CaptureStage.bits 7 0x63),
    opcodeLoad := Modules.EqualsConstant.design
      (.vector 7 .bit) (CaptureStage.bits 7 0x03),
    opcodeStore := Modules.EqualsConstant.design
      (.vector 7 .bit) (CaptureStage.bits 7 0x23),
    opcodeAluImm := Modules.EqualsConstant.design
      (.vector 7 .bit) (CaptureStage.bits 7 0x13),
    opcodeAluReg := Modules.EqualsConstant.design
      (.vector 7 .bit) (CaptureStage.bits 7 0x33),
    funct3Zero := Modules.EqualsConstant.design
      (.vector 3 .bit) (CaptureStage.bits 3 0),
    jalr := Primitives.andDesign,
    zero := Modules.Constant.design .bit false,
    immediate := Modules.VectorLayout.design 32 32 CaptureStage.immediateJLayout,
    storedNext := Modules.NamedTupleCombiner.designWith
      CaptureStage.storedMap CaptureStage.Stored.schema,
    stored := Modules.EnabledRegister.designWith CaptureStage.storedType
      CaptureStage.Stored.schema,
    storedOutputs := Modules.NamedTupleSplitter.designWith
      CaptureStage.storedMap CaptureStage.Stored.schema,
    branch := Modules.EnabledResetRegister.design .bit false }
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
  instance (.captureEnable) {
    .left := input.mem_do_rinst,
    .right := input.mem_done }
  instance (.reset) {
    .input := input.resetn }
  instance (.opcode) {
    .value := input.mem_rdata_latched }
  instance (.funct3) {
    .value := input.mem_rdata_latched }
  instance (.decodedRd) {
    .value := input.mem_rdata_latched }
  instance (.decodedRs1) {
    .value := input.mem_rdata_latched }
  instance (.decodedRs2) {
    .value := input.mem_rdata_latched }
  instance (.opcodeLui) {
    .value := opcode.result }
  instance (.opcodeAuipc) {
    .value := opcode.result }
  instance (.opcodeJal) {
    .value := opcode.result }
  instance (.opcodeJalr) {
    .value := opcode.result }
  instance (.opcodeBranch) {
    .value := opcode.result }
  instance (.opcodeLoad) {
    .value := opcode.result }
  instance (.opcodeStore) {
    .value := opcode.result }
  instance (.opcodeAluImm) {
    .value := opcode.result }
  instance (.opcodeAluReg) {
    .value := opcode.result }
  instance (.funct3Zero) {
    .value := funct3.result }
  instance (.jalr) {
    .left := opcodeJalr.result,
    .right := funct3Zero.result }
  instance (.zero) {}
  instance (.immediate) {
    .input := input.mem_rdata_latched }
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
  instance (.stored) {
    .data := storedNext.value,
    .enable := captureEnable.output }
  instance (.storedOutputs) {
    .value := stored.q }
  instance (.branch) {
    .value := opcodeBranch.result,
    .enable := captureEnable.output,
    .reset := reset.output }
  }

end Silean.Examples.PicoRV.Decoder

namespace Silean.Examples.PicoRV.Decoder.CaptureStage

/-! ## Behavioral contract -/

structure Inputs where
  resetn : Bool
  mem_do_rinst : Bool
  mem_done : Bool
  mem_rdata_latched : Word

def valuesOf (inputs : inputMap.Values) : Inputs where
  resetn := inputs .resetn
  mem_do_rinst := inputs .mem_do_rinst
  mem_done := inputs .mem_done
  mem_rdata_latched := inputs .mem_rdata_latched

def opcodeBits (word : Word) : Fin 7 → Bool :=
  Modules.VectorSlice.slice (prefixWidth := 0) (width := 7) (suffixWidth := 25) word

def funct3Bits (word : Word) : Fin 3 → Bool :=
  Modules.VectorSlice.slice (prefixWidth := 12) (width := 3) (suffixWidth := 17) word

def addressBits (low : Nat) (suffix : Nat)
    (word : Fin (low + 5 + suffix) → Bool) : RegisterAddress :=
  Modules.VectorSlice.slice (prefixWidth := low) (width := 5) (suffixWidth := suffix) word

def matchesBits (width value : Nat) (actual : Fin width → Bool) : Bool :=
  (SignalType.vector width .bit).equal actual (bits width value)

def immediateJBits (word : Word) : Word :=
  Modules.VectorLayout.apply immediateJLayout word

def captured (inputs : Inputs) (state : stateMap.Values) : stateMap.Values :=
  if !(inputs.mem_do_rinst && inputs.mem_done) then state else
  let word := inputs.mem_rdata_latched
  let state := stateMap.set state .instr_lui (matchesBits 7 0x37 (opcodeBits word))
  let state := stateMap.set state .instr_auipc (matchesBits 7 0x17 (opcodeBits word))
  let state := stateMap.set state .instr_jal (matchesBits 7 0x6f (opcodeBits word))
  let state := stateMap.set state .instr_jalr
    (matchesBits 7 0x67 (opcodeBits word) && matchesBits 3 0 (funct3Bits word))
  let state := stateMap.set state .is_beq_bne_blt_bge_bltu_bgeu
    (matchesBits 7 0x63 (opcodeBits word))
  let state := stateMap.set state .is_lb_lh_lw_lbu_lhu
    (matchesBits 7 0x03 (opcodeBits word))
  let state := stateMap.set state .is_sb_sh_sw (matchesBits 7 0x23 (opcodeBits word))
  let state := stateMap.set state .is_alu_reg_imm (matchesBits 7 0x13 (opcodeBits word))
  let state := stateMap.set state .is_alu_reg_reg (matchesBits 7 0x33 (opcodeBits word))
  let state := stateMap.set state .decoded_rd (addressBits 7 20 word)
  let state := stateMap.set state .decoded_rs1 (addressBits 15 12 word)
  let state := stateMap.set state .decoded_rs2 (addressBits 20 7 word)
  let state := stateMap.set state .decoded_imm_j (immediateJBits word)
  stateMap.set state .compressed_instr false

def nextState (inputs : Inputs) (state : stateMap.Values) : stateMap.Values :=
  let state := captured inputs state
  if inputs.resetn then state else
    stateMap.set state .is_beq_bne_blt_bge_bltu_bgeu false

def outputRule : Contracts.Cycle.CycleOutputRule ports stateMap where
  readsInputs := .empty inputMap
  writesOutputs := .all stateMap
  target _ state := state

def stateRule : Contracts.Cycle.CycleStateRule ports stateMap where
  readsInputs := .all inputMap
  target inputs state := nextState (valuesOf inputs) state

@[simp] theorem outputRule_writes (output : Output) :
    output ∈ outputRule.writesOutputs.labels := by
  change output ∈ (SignalGroup.all stateMap).labels
  rw [SignalGroup.all_labels]
  exact (stateMap.labels.locate output).mem

@[simp] theorem stateRule_reads (input : Input) :
    input ∈ stateRule.readsInputs.labels := by
  change input ∈ (SignalGroup.all inputMap).labels
  rw [SignalGroup.all_labels]
  exact (inputMap.labels.locate input).mem

module_cycle_contract cycleContract for ports where
  state := stateMap
  output_rule outputs := outputRule
  state_rule := stateRule

@[simp] theorem outputRule_holds_iff
    (inputs : ports.inputs.Values) (state : stateMap.Values)
    (outputs : ports.outputs.Values) :
    outputRule.Holds inputs state outputs ↔ outputs = state := by
  simp [outputRule, Contracts.Cycle.CycleOutputRule.Holds]

end Silean.Examples.PicoRV.Decoder.CaptureStage
