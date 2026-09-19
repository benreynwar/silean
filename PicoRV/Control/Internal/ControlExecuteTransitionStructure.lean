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
definition in `ControlExecuteTransition.lean`. -/

module_design ExecuteTransition (name := "picorv32_control_execute_transition") where
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
    zeroRd (name := .indexed "constant" 2) :=
      Silean.Modules.Constant.design (.vector 5 .bit) (fiveBitsOfNat 0),
    fetchState (name := .indexed "constant" 3) :=
      Silean.Modules.Constant.design (.vector 8 .bit) (stateBits cpuStateFetch),
    branchPhase (name := .indexed "mux" 0) :=
      Silean.Modules.Mux.design (.vector 8 .bit),
    branchDecoder (name := .indexed "bit_mux" 0) := Silean.Modules.BitMux.design,
    branchState (name := .indexed "named_tuple_combiner" 0) :=
      Silean.Modules.NamedTupleCombiner.designWith
      stateMap ControlState.schema,
    branchTransition (name := .indexed "named_tuple_combiner" 1) :=
      Silean.Modules.NamedTupleCombiner.designWith
      TransitionValue.signalMap TransitionValue.schema,
    ordinaryState (name := .indexed "named_tuple_combiner" 2) :=
      Silean.Modules.NamedTupleCombiner.designWith
      stateMap ControlState.schema,
    ordinaryTransition (name := .indexed "named_tuple_combiner" 3) :=
      Silean.Modules.NamedTupleCombiner.designWith
      TransitionValue.signalMap TransitionValue.schema,
    result (name := .indexed "mux" 1) :=
      Silean.Modules.Mux.design transitionType }
  wiring {
  outputs { .transition := result.result }
  instance (.inputsFields) { .value := input.inputs }
  instance (.updatedFields) { .value := input.updated }
  instance (.falseBit) {}
  instance (.trueBit) {}
  instance (.zeroRd) {}
  instance (.fetchState) {}
  instance (.branchPhase) {
    .select := inputsFields[.mem_done],
    .whenFalse := updatedFields[.cpu_state],
    .whenTrue := fetchState.output }
  instance (.branchDecoder) {
    .select := inputsFields[.alu_out_0],
    .whenFalse := updatedFields[.decoder_trigger],
    .whenTrue := falseBit.output }
  instance (.branchState) {
    .cpu_state := branchPhase.result,
    .latched_store := inputsFields[.alu_out_0],
    .latched_stalu := updatedFields[.latched_stalu],
    .latched_branch := inputsFields[.alu_out_0],
    .latched_is_lu := updatedFields[.latched_is_lu],
    .latched_is_lh := updatedFields[.latched_is_lh],
    .latched_is_lb := updatedFields[.latched_is_lb],
    .latched_rd := zeroRd.output,
    .mem_wordsize := updatedFields[.mem_wordsize],
    .mem_do_prefetch := updatedFields[.mem_do_prefetch],
    .mem_do_rinst := updatedFields[.mem_do_rinst],
    .mem_do_rdata := updatedFields[.mem_do_rdata],
    .mem_do_wdata := updatedFields[.mem_do_wdata],
    .decoder_trigger := branchDecoder.result,
    .decoder_pseudo_trigger := updatedFields[.decoder_pseudo_trigger],
    .trap := updatedFields[.trap] }
  instance (.branchTransition) {
    .state := branchState.value,
    .setRinst := inputsFields[.alu_out_0],
    .setRdata := falseBit.output,
    .setWdata := falseBit.output }
  instance (.ordinaryState) {
    .cpu_state := fetchState.output,
    .latched_store := trueBit.output,
    .latched_stalu := trueBit.output,
    .latched_branch := inputsFields[.instr_jalr],
    .latched_is_lu := updatedFields[.latched_is_lu],
    .latched_is_lh := updatedFields[.latched_is_lh],
    .latched_is_lb := updatedFields[.latched_is_lb],
    .latched_rd := updatedFields[.latched_rd],
    .mem_wordsize := updatedFields[.mem_wordsize],
    .mem_do_prefetch := updatedFields[.mem_do_prefetch],
    .mem_do_rinst := updatedFields[.mem_do_rinst],
    .mem_do_rdata := updatedFields[.mem_do_rdata],
    .mem_do_wdata := updatedFields[.mem_do_wdata],
    .decoder_trigger := updatedFields[.decoder_trigger],
    .decoder_pseudo_trigger := updatedFields[.decoder_pseudo_trigger],
    .trap := updatedFields[.trap] }
  instance (.ordinaryTransition) {
    .state := ordinaryState.value,
    .setRinst := falseBit.output,
    .setRdata := falseBit.output,
    .setWdata := falseBit.output }
  instance (.result) {
    .select := inputsFields[.is_beq_bne_blt_bge_bltu_bgeu],
    .whenFalse := ordinaryTransition.value,
    .whenTrue := branchTransition.value }
  }

end PicoRV.Control
