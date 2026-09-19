import PicoRV.Control.ControlNextContracts
import Silean.Authoring.ModuleDesign
import Silean.Modules.BitMux.BitMux
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.Mux
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter

namespace PicoRV.Control

open Silean
open Silean.Authoring

/-! Expanded typed production structure corresponding to the concise authored
definition in `ControlLoadRs2Transition.lean`. -/

module_design LoadRs2Transition
    (name := "picorv32_control_load_rs2_transition") where
  boundary (PhaseTransition.ports) (naming := PhaseTransition.Naming.ports)
  instances {
    inputsFields (name := .indexed "named_tuple_splitter" 0) :=
      Silean.Modules.NamedTupleSplitter.designWith
      ControlInputs.signalMap ControlInputs.schema,
    updatedFields (name := .indexed "named_tuple_splitter" 1) :=
      Silean.Modules.NamedTupleSplitter.designWith
      stateMap ControlState.schema,
    falseBit (name := .indexed "constant" 0) :=
      Silean.Modules.Constant.design .bit false,
    trueBit (name := .indexed "constant" 1) :=
      Silean.Modules.Constant.design .bit true,
    executeState (name := .indexed "constant" 2) :=
      Silean.Modules.Constant.design (.vector 8 .bit) (stateBits cpuStateExec),
    shiftState (name := .indexed "constant" 3) :=
      Silean.Modules.Constant.design (.vector 8 .bit) (stateBits cpuStateShift),
    storeState (name := .indexed "constant" 4) :=
      Silean.Modules.Constant.design (.vector 8 .bit) (stateBits cpuStateStmem),
    shiftPhase (name := .indexed "mux" 0) :=
      Silean.Modules.Mux.design (.vector 8 .bit),
    shiftRinst (name := .indexed "bit_mux" 0) := Silean.Modules.BitMux.design,
    storePhase (name := .indexed "mux" 1) :=
      Silean.Modules.Mux.design (.vector 8 .bit),
    storeRinst (name := .indexed "bit_mux" 1) := Silean.Modules.BitMux.design,
    resultState (name := .indexed "named_tuple_combiner" 0) :=
      Silean.Modules.NamedTupleCombiner.designWith
      stateMap ControlState.schema,
    result (name := .indexed "named_tuple_combiner" 1) :=
      Silean.Modules.NamedTupleCombiner.designWith
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

end PicoRV.Control
