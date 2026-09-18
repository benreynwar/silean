import PicoRV.Datapath.DatapathNextContracts
import Silean.Authoring.ModuleDesign
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.Mux
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Modules.VectorLayout.VectorLayout

namespace PicoRV.Datapath

open Silean
open Silean.Authoring

def LoadRs1Update.lowFiveLayout (index : Fin 5) :
    Silean.Modules.VectorLayout.BitSource 32 := .input ⟨index.val, by omega⟩

/-! Operand capture with the exact source priority. The mux chains are built
from the default case upward, ending with `instr_trap`, so overlaps have the
same meaning as the Verilog `case (1'b1)`. -/
module_design LoadRs1Update (name := "picorv32_datapath_load_rs1_update") where
  boundary (StateUpdate.ports) (naming := StateUpdate.Naming.ports)
  instances {
    inputsFields := Silean.Modules.NamedTupleSplitter.designWith
      DatapathInputs.signalMap DatapathInputs.schema,
    currentFields := Silean.Modules.NamedTupleSplitter.designWith
      stateMap DatapathState.schema,
    updatedFields := Silean.Modules.NamedTupleSplitter.designWith
      stateMap DatapathState.schema,
    zeroWord := Silean.Modules.Constant.design (.vector 32 .bit) (wordOfNat 0),
    lowFiveRs2 := Silean.Modules.VectorLayout.design 32 5 LoadRs1Update.lowFiveLayout,
    luiOperand := Silean.Modules.Mux.design (.vector 32 .bit),
    selectedOp1 := Silean.Modules.Mux.design (.vector 32 .bit),
    trapOp1 := Silean.Modules.Mux.design (.vector 32 .bit),
    op2Immediate := Silean.Modules.Mux.design (.vector 32 .bit),
    op2Shift := Silean.Modules.Mux.design (.vector 32 .bit),
    op2Load := Silean.Modules.Mux.design (.vector 32 .bit),
    op2Lui := Silean.Modules.Mux.design (.vector 32 .bit),
    trapOp2 := Silean.Modules.Mux.design (.vector 32 .bit),
    shiftImmediate := Silean.Modules.Mux.design (.vector 5 .bit),
    shiftLoad := Silean.Modules.Mux.design (.vector 5 .bit),
    shiftLui := Silean.Modules.Mux.design (.vector 5 .bit),
    trapShift := Silean.Modules.Mux.design (.vector 5 .bit),
    finalShift := Silean.Modules.Mux.design (.vector 5 .bit),
    result := Silean.Modules.NamedTupleCombiner.designWith
      stateMap DatapathState.schema }
  wiring {
  outputs { .state := result.value }
  instance (.inputsFields) { .value := input.inputs }
  instance (.currentFields) { .value := input.current }
  instance (.updatedFields) { .value := input.updated }
  instance (.zeroWord) {}
  instance (.lowFiveRs2) { .input := inputsFields[.cpuregs_rs2] }
  instance (.luiOperand) {
    .select := inputsFields[.instr_lui],
    .whenFalse := currentFields[.reg_pc],
    .whenTrue := zeroWord.output }
  instance (.selectedOp1) {
    .select := inputsFields[.is_lui_auipc_jal],
    .whenFalse := inputsFields[.cpuregs_rs1],
    .whenTrue := luiOperand.result }
  instance (.trapOp1) {
    .select := inputsFields[.instr_trap],
    .whenFalse := selectedOp1.result,
    .whenTrue := updatedFields[.reg_op1] }

  instance (.op2Immediate) {
    .select := inputsFields[.is_jalr_addi_slti_sltiu_xori_ori_andi],
    .whenFalse := inputsFields[.cpuregs_rs2],
    .whenTrue := inputsFields[.decoded_imm] }
  instance (.op2Shift) {
    .select := inputsFields[.is_slli_srli_srai],
    .whenFalse := op2Immediate.result,
    .whenTrue := updatedFields[.reg_op2] }
  instance (.op2Load) {
    .select := inputsFields[.is_lb_lh_lw_lbu_lhu],
    .whenFalse := op2Shift.result,
    .whenTrue := updatedFields[.reg_op2] }
  instance (.op2Lui) {
    .select := inputsFields[.is_lui_auipc_jal],
    .whenFalse := op2Load.result,
    .whenTrue := inputsFields[.decoded_imm] }
  instance (.trapOp2) {
    .select := inputsFields[.instr_trap],
    .whenFalse := op2Lui.result,
    .whenTrue := updatedFields[.reg_op2] }

  instance (.shiftImmediate) {
    .select := inputsFields[.is_jalr_addi_slti_sltiu_xori_ori_andi],
    .whenFalse := lowFiveRs2.output,
    .whenTrue := updatedFields[.reg_sh] }
  instance (.shiftLoad) {
    .select := inputsFields[.is_slli_srli_srai],
    .whenFalse := shiftImmediate.result,
    .whenTrue := inputsFields[.decoded_rs2] }
  instance (.shiftLui) {
    .select := inputsFields[.is_lb_lh_lw_lbu_lhu],
    .whenFalse := shiftLoad.result,
    .whenTrue := updatedFields[.reg_sh] }
  instance (.trapShift) {
    .select := inputsFields[.is_lui_auipc_jal],
    .whenFalse := shiftLui.result,
    .whenTrue := updatedFields[.reg_sh] }
  instance (.finalShift) {
    .select := inputsFields[.instr_trap],
    .whenFalse := trapShift.result,
    .whenTrue := updatedFields[.reg_sh] }
  instance (.result) {
    .reg_pc := updatedFields[.reg_pc],
    .reg_next_pc := updatedFields[.reg_next_pc],
    .reg_op1 := trapOp1.result,
    .reg_op2 := trapOp2.result,
    .reg_out := updatedFields[.reg_out],
    .reg_sh := finalShift.result,
    .alu_out_q := updatedFields[.alu_out_q] }
  }

end PicoRV.Datapath
