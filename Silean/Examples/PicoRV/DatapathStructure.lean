import Silean.Examples.PicoRV.Alu
import Silean.Examples.PicoRV.Datapath.DatapathFetchUpdate
import Silean.Examples.PicoRV.Datapath.DatapathNext
import Silean.Authoring.ModuleDesign
import Silean.Modules.Add.Add
import Silean.Modules.Constant.Constant
import Silean.Modules.EqualsConstant.EqualsConstant
import Silean.Modules.Mux.MuxStructure
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Modules.Register.Register
import Silean.Modules.VectorLayout.VectorLayout
import Silean.Primitives.And

namespace Silean.Examples.PicoRV

open Silean
open Silean.Authoring

/-! The stateful datapath stores all seven source registers in one aggregate
register. The current tuple feeds the ALU, public combinational outputs, and
`Datapath.Next`; the certified next-state tuple is captured on the next edge.
The ALU remains outside `Next` so its comparison is observable immediately
while its word result is also captured into `alu_out_q`, matching the source's
nonblocking timing. -/
module_design Datapath (name := "picorv32_datapath") where
  boundary (Datapath.ports) (naming := Datapath.Naming.ports)
  instances {
    inputsValue := Modules.NamedTupleCombiner.designWith
      Datapath.DatapathInputs.signalMap Datapath.DatapathInputs.schema,
    storage := Modules.Register.designWith Datapath.DatapathState.schema,
    stateFields := Modules.NamedTupleSplitter.designWith
      Datapath.stateMap Datapath.DatapathState.schema,
    alu := Alu.design,
    next := Datapath.Next.design,
    branchActive := Primitives.andDesign,
    alignedRegOut := Modules.VectorLayout.design 32 32
      Datapath.FetchUpdate.clearLowLayout,
    nextPc := Modules.Mux.design (.vector 32 .bit),
    fetchPhase := Modules.EqualsConstant.design (.vector 8 .bit)
      (Datapath.stateBits Datapath.cpuStateFetch),
    falseBit := Modules.Constant.design .bit false,
    zeroWord := Modules.Constant.design (.vector 32 .bit) (Datapath.wordOfNat 0),
    four := Modules.Constant.design (.vector 32 .bit) (Datapath.wordOfNat 4),
    linkValue := Modules.Add.design 32,
    storeSource := Modules.Mux.design (.vector 32 .bit),
    storedValue := Modules.Mux.design (.vector 32 .bit),
    fetchValue := Modules.Mux.design (.vector 32 .bit),
    writeback := Modules.Mux.design (.vector 32 .bit) }
  wiring {
  outputs {
    .reg_pc := stateFields[.reg_pc],
    .reg_op1 := stateFields[.reg_op1],
    .reg_op2 := stateFields[.reg_op2],
    .reg_sh := stateFields[.reg_sh],
    .next_pc := nextPc.result,
    .alu_out_0 := alu.alu_out_0,
    .cpuregs_wrdata := writeback.result }
  instance (.inputsValue) {
    .resetn := input.resetn,
    .cpu_state := input.cpu_state,
    .latched_store := input.latched_store,
    .latched_stalu := input.latched_stalu,
    .latched_branch := input.latched_branch,
    .latched_is_lu := input.latched_is_lu,
    .latched_is_lh := input.latched_is_lh,
    .latched_is_lb := input.latched_is_lb,
    .mem_do_prefetch := input.mem_do_prefetch,
    .mem_do_rdata := input.mem_do_rdata,
    .mem_do_wdata := input.mem_do_wdata,
    .decoder_trigger := input.decoder_trigger,
    .instr_lui := input.instr_lui,
    .instr_jal := input.instr_jal,
    .instr_trap := input.instr_trap,
    .instr_sub := input.instr_sub,
    .instr_beq := input.instr_beq,
    .instr_bne := input.instr_bne,
    .instr_bge := input.instr_bge,
    .instr_bgeu := input.instr_bgeu,
    .instr_xori := input.instr_xori,
    .instr_xor := input.instr_xor,
    .instr_ori := input.instr_ori,
    .instr_or := input.instr_or,
    .instr_andi := input.instr_andi,
    .instr_and := input.instr_and,
    .instr_slli := input.instr_slli,
    .instr_srli := input.instr_srli,
    .instr_srai := input.instr_srai,
    .instr_sll := input.instr_sll,
    .instr_srl := input.instr_srl,
    .instr_sra := input.instr_sra,
    .is_lui_auipc_jal := input.is_lui_auipc_jal,
    .is_lb_lh_lw_lbu_lhu := input.is_lb_lh_lw_lbu_lhu,
    .is_slli_srli_srai := input.is_slli_srli_srai,
    .is_jalr_addi_slti_sltiu_xori_ori_andi :=
      input.is_jalr_addi_slti_sltiu_xori_ori_andi,
    .is_lui_auipc_jal_jalr_addi_add_sub :=
      input.is_lui_auipc_jal_jalr_addi_add_sub,
    .is_slti_blt_slt := input.is_slti_blt_slt,
    .is_sltiu_bltu_sltu := input.is_sltiu_bltu_sltu,
    .is_compare := input.is_compare,
    .decoded_imm := input.decoded_imm,
    .decoded_imm_j := input.decoded_imm_j,
    .decoded_rs2 := input.decoded_rs2,
    .cpuregs_rs1 := input.cpuregs_rs1,
    .cpuregs_rs2 := input.cpuregs_rs2,
    .mem_done := input.mem_done,
    .mem_rdata_word := input.mem_rdata_word }
  instance (.storage) { .input := next.state }
  instance (.stateFields) { .value := storage.output }
  instance (.alu) {
    .reg_op1 := stateFields[.reg_op1],
    .reg_op2 := stateFields[.reg_op2],
    .instr_sub := input.instr_sub,
    .instr_beq := input.instr_beq,
    .instr_bne := input.instr_bne,
    .instr_bge := input.instr_bge,
    .instr_bgeu := input.instr_bgeu,
    .is_slti_blt_slt := input.is_slti_blt_slt,
    .is_sltiu_bltu_sltu := input.is_sltiu_bltu_sltu,
    .is_lui_auipc_jal_jalr_addi_add_sub :=
      input.is_lui_auipc_jal_jalr_addi_add_sub,
    .is_compare := input.is_compare,
    .instr_xori := input.instr_xori,
    .instr_xor := input.instr_xor,
    .instr_ori := input.instr_ori,
    .instr_or := input.instr_or,
    .instr_andi := input.instr_andi,
    .instr_and := input.instr_and }
  instance (.next) {
    .inputs := inputsValue.value,
    .current := storage.output,
    .alu_out := alu.alu_out }
  instance (.branchActive) {
    .left := input.latched_store,
    .right := input.latched_branch }
  instance (.alignedRegOut) { .input := stateFields[.reg_out] }
  instance (.nextPc) {
    .select := branchActive.output,
    .whenFalse := stateFields[.reg_next_pc],
    .whenTrue := alignedRegOut.output }
  instance (.fetchPhase) { .value := input.cpu_state }
  instance (.falseBit) {}
  instance (.zeroWord) {}
  instance (.four) {}
  instance (.linkValue) {
    .left := stateFields[.reg_pc],
    .right := four.output,
    .carryIn := falseBit.output }
  instance (.storeSource) {
    .select := input.latched_stalu,
    .whenFalse := stateFields[.reg_out],
    .whenTrue := stateFields[.alu_out_q] }
  instance (.storedValue) {
    .select := input.latched_store,
    .whenFalse := zeroWord.output,
    .whenTrue := storeSource.result }
  instance (.fetchValue) {
    .select := input.latched_branch,
    .whenFalse := storedValue.result,
    .whenTrue := linkValue.result }
  instance (.writeback) {
    .select := fetchPhase.result,
    .whenFalse := zeroWord.output,
    .whenTrue := fetchValue.result }
  }

end Silean.Examples.PicoRV
