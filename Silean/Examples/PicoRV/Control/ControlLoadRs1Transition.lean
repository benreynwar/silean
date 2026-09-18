import Silean.Examples.PicoRV.Control.ControlNextContracts
import Silean.Authoring.ModuleDesign
import Silean.Modules.BitMux.BitMux
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.Mux
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter

namespace Silean.Examples.PicoRV.Control

open Silean
open Silean.Authoring

/-! Load-RS1 is an ordered decoder, not a one-hot selection. Two parallel mux
chains preserve that order for both fields it can change: `cpu_state` and
`mem_do_rinst`. This matters for arbitrary overlapping decoder inputs, which
the universal contract does not rule out. -/

module_design LoadRs1Transition
    (name := "picorv32_control_load_rs1_transition") where
  boundary (PhaseTransition.ports) (naming := PhaseTransition.Naming.ports)
  instances {
    inputsFields := Modules.NamedTupleSplitter.designWith
      ControlInputs.signalMap ControlInputs.schema,
    updatedFields := Modules.NamedTupleSplitter.designWith
      stateMap ControlState.schema,
    falseBit := Modules.Constant.design .bit false,
    trueBit := Modules.Constant.design .bit true,
    trapState := Modules.Constant.design (.vector 8 .bit)
      (stateBits cpuStateTrap),
    executeState := Modules.Constant.design (.vector 8 .bit)
      (stateBits cpuStateExec),
    loadState := Modules.Constant.design (.vector 8 .bit)
      (stateBits cpuStateLdmem),
    shiftState := Modules.Constant.design (.vector 8 .bit)
      (stateBits cpuStateShift),
    storeState := Modules.Constant.design (.vector 8 .bit)
      (stateBits cpuStateStmem),
    regShiftPhase := Modules.Mux.design (.vector 8 .bit),
    regShiftRinst := Modules.BitMux.design,
    storePhase := Modules.Mux.design (.vector 8 .bit),
    storeRinst := Modules.BitMux.design,
    immediateAluPhase := Modules.Mux.design (.vector 8 .bit),
    immediateAluRinst := Modules.BitMux.design,
    immediateShiftPhase := Modules.Mux.design (.vector 8 .bit),
    immediateShiftRinst := Modules.BitMux.design,
    loadPhase := Modules.Mux.design (.vector 8 .bit),
    loadRinst := Modules.BitMux.design,
    directPhase := Modules.Mux.design (.vector 8 .bit),
    directRinst := Modules.BitMux.design,
    trapPhase := Modules.Mux.design (.vector 8 .bit),
    trapRinst := Modules.BitMux.design,
    resultState := Modules.NamedTupleCombiner.designWith
      stateMap ControlState.schema,
    result := Modules.NamedTupleCombiner.designWith
      TransitionValue.signalMap TransitionValue.schema }
  wiring {
  outputs { .transition := result.value }
  instance (.inputsFields) { .value := input.inputs }
  instance (.updatedFields) { .value := input.updated }
  instance (.falseBit) {}
  instance (.trueBit) {}
  instance (.trapState) {}
  instance (.executeState) {}
  instance (.loadState) {}
  instance (.shiftState) {}
  instance (.storeState) {}
  instance (.regShiftPhase) {
    .select := inputsFields[.is_sll_srl_sra],
    .whenFalse := executeState.output,
    .whenTrue := shiftState.output }
  instance (.regShiftRinst) {
    .select := inputsFields[.is_sll_srl_sra],
    .whenFalse := updatedFields[.mem_do_prefetch],
    .whenTrue := updatedFields[.mem_do_rinst] }
  instance (.storePhase) {
    .select := inputsFields[.is_sb_sh_sw],
    .whenFalse := regShiftPhase.result,
    .whenTrue := storeState.output }
  instance (.storeRinst) {
    .select := inputsFields[.is_sb_sh_sw],
    .whenFalse := regShiftRinst.result,
    .whenTrue := trueBit.output }
  instance (.immediateAluPhase) {
    .select := inputsFields[.is_jalr_addi_slti_sltiu_xori_ori_andi],
    .whenFalse := storePhase.result,
    .whenTrue := executeState.output }
  instance (.immediateAluRinst) {
    .select := inputsFields[.is_jalr_addi_slti_sltiu_xori_ori_andi],
    .whenFalse := storeRinst.result,
    .whenTrue := updatedFields[.mem_do_prefetch] }
  instance (.immediateShiftPhase) {
    .select := inputsFields[.is_slli_srli_srai],
    .whenFalse := immediateAluPhase.result,
    .whenTrue := shiftState.output }
  instance (.immediateShiftRinst) {
    .select := inputsFields[.is_slli_srli_srai],
    .whenFalse := immediateAluRinst.result,
    .whenTrue := updatedFields[.mem_do_rinst] }
  instance (.loadPhase) {
    .select := inputsFields[.is_lb_lh_lw_lbu_lhu],
    .whenFalse := immediateShiftPhase.result,
    .whenTrue := loadState.output }
  instance (.loadRinst) {
    .select := inputsFields[.is_lb_lh_lw_lbu_lhu],
    .whenFalse := immediateShiftRinst.result,
    .whenTrue := trueBit.output }
  instance (.directPhase) {
    .select := inputsFields[.is_lui_auipc_jal],
    .whenFalse := loadPhase.result,
    .whenTrue := executeState.output }
  instance (.directRinst) {
    .select := inputsFields[.is_lui_auipc_jal],
    .whenFalse := loadRinst.result,
    .whenTrue := updatedFields[.mem_do_prefetch] }
  instance (.trapPhase) {
    .select := inputsFields[.instr_trap],
    .whenFalse := directPhase.result,
    .whenTrue := trapState.output }
  instance (.trapRinst) {
    .select := inputsFields[.instr_trap],
    .whenFalse := directRinst.result,
    .whenTrue := updatedFields[.mem_do_rinst] }
  instance (.resultState) {
    .cpu_state := trapPhase.result,
    .latched_store := updatedFields[.latched_store],
    .latched_stalu := updatedFields[.latched_stalu],
    .latched_branch := updatedFields[.latched_branch],
    .latched_is_lu := updatedFields[.latched_is_lu],
    .latched_is_lh := updatedFields[.latched_is_lh],
    .latched_is_lb := updatedFields[.latched_is_lb],
    .latched_rd := updatedFields[.latched_rd],
    .mem_wordsize := updatedFields[.mem_wordsize],
    .mem_do_prefetch := updatedFields[.mem_do_prefetch],
    .mem_do_rinst := trapRinst.result,
    .mem_do_rdata := updatedFields[.mem_do_rdata],
    .mem_do_wdata := updatedFields[.mem_do_wdata],
    .decoder_trigger := updatedFields[.decoder_trigger],
    .decoder_pseudo_trigger := updatedFields[.decoder_pseudo_trigger],
    .trap := updatedFields[.trap] }
  instance (.result) {
    .state := resultState.value,
    .setRinst := falseBit.output,
    .setRdata := falseBit.output,
    .setWdata := falseBit.output }
  }

end Silean.Examples.PicoRV.Control
