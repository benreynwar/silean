import Silean.Examples.PicoRV.Control.ControlNextContracts
import Silean.Authoring.ModuleDesign
import Silean.Modules.BitMux.BitMux
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.Mux
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter

namespace Silean.Examples.PicoRV.Control

open Silean
open Silean.Authoring

/-! Load-RS2 preserves the source's ordered three-way decision: stores have
priority over register shifts, and every other instruction enters execute.
Parallel mux chains select the next phase and instruction-read command without
assuming that the two decoder selectors are mutually exclusive. -/

module_design LoadRs2Transition
    (name := "picorv32_control_load_rs2_transition") where
  boundary (PhaseTransition.ports) (naming := PhaseTransition.Naming.ports)
  instances {
    inputsFields := Modules.NamedTupleSplitter.designWith
      ControlInputs.signalMap ControlInputs.schema,
    updatedFields := Modules.NamedTupleSplitter.designWith
      stateMap ControlState.schema,
    falseBit := Modules.Constant.design .bit false,
    trueBit := Modules.Constant.design .bit true,
    executeState := Modules.Constant.design (.vector 8 .bit)
      (stateBits cpuStateExec),
    shiftState := Modules.Constant.design (.vector 8 .bit)
      (stateBits cpuStateShift),
    storeState := Modules.Constant.design (.vector 8 .bit)
      (stateBits cpuStateStmem),
    shiftPhase := Modules.Mux.design (.vector 8 .bit),
    shiftRinst := Modules.BitMux.design,
    storePhase := Modules.Mux.design (.vector 8 .bit),
    storeRinst := Modules.BitMux.design,
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
  instance (.executeState) {}
  instance (.shiftState) {}
  instance (.storeState) {}
  instance (.shiftPhase) {
    .select := inputsFields[.is_sll_srl_sra],
    .whenFalse := executeState.output,
    .whenTrue := shiftState.output }
  instance (.shiftRinst) {
    .select := inputsFields[.is_sll_srl_sra],
    .whenFalse := updatedFields[.mem_do_prefetch],
    .whenTrue := updatedFields[.mem_do_rinst] }
  instance (.storePhase) {
    .select := inputsFields[.is_sb_sh_sw],
    .whenFalse := shiftPhase.result,
    .whenTrue := storeState.output }
  instance (.storeRinst) {
    .select := inputsFields[.is_sb_sh_sw],
    .whenFalse := shiftRinst.result,
    .whenTrue := trueBit.output }
  instance (.resultState) {
    .cpu_state := storePhase.result,
    .latched_store := updatedFields[.latched_store],
    .latched_stalu := updatedFields[.latched_stalu],
    .latched_branch := updatedFields[.latched_branch],
    .latched_is_lu := updatedFields[.latched_is_lu],
    .latched_is_lh := updatedFields[.latched_is_lh],
    .latched_is_lb := updatedFields[.latched_is_lb],
    .latched_rd := updatedFields[.latched_rd],
    .mem_wordsize := updatedFields[.mem_wordsize],
    .mem_do_prefetch := updatedFields[.mem_do_prefetch],
    .mem_do_rinst := storeRinst.result,
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
