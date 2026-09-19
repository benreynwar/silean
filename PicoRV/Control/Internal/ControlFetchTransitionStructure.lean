import PicoRV.Control.ControlNextContracts
import Silean.Authoring.ModuleDesign
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.Mux
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Naming.PrimitiveNaming

namespace PicoRV.Control

open Silean
open Silean.Authoring

/-! Expanded typed production structure corresponding to the concise Fetch
transition definition in `ControlFetchTransition.lean`. -/

module_design FetchTransition (name := "picorv32_control_fetch_transition") where
  boundary (PhaseTransition.ports) (naming := PhaseTransition.Naming.ports)
  instances {
    inputsFields (name := .indexed "named_tuple_splitter" 0) :=
      Silean.Modules.NamedTupleSplitter.designWith
      ControlInputs.signalMap ControlInputs.schema,
    currentFields (name := .indexed "named_tuple_splitter" 1) :=
      Silean.Modules.NamedTupleSplitter.designWith
      stateMap ControlState.schema,
    updatedFields (name := .indexed "named_tuple_splitter" 2) :=
      Silean.Modules.NamedTupleSplitter.designWith
      stateMap ControlState.schema,
    falseBit (name := .indexed "constant" 0) :=
      Silean.Modules.Constant.design .bit false,
    trueBit (name := .indexed "constant" 1) :=
      Silean.Modules.Constant.design .bit true,
    wordSize (name := .indexed "constant" 2) :=
      Silean.Modules.Constant.design (.vector 2 .bit) (twoBitsOfNat 0),
    loadRs1State (name := .indexed "constant" 3) :=
      Silean.Modules.Constant.design (.vector 8 .bit)
      (stateBits cpuStateLdRs1),
    notDecoder (name := .indexed "not" 0) := Silean.Primitives.notDesign,
    notJalr (name := .indexed "not" 1) := Silean.Primitives.notDesign,
    commonState (name := .indexed "named_tuple_combiner" 0) :=
      Silean.Modules.NamedTupleCombiner.designWith
      stateMap ControlState.schema,
    commonFields (name := .indexed "named_tuple_splitter" 3) :=
      Silean.Modules.NamedTupleSplitter.designWith
      stateMap ControlState.schema,
    jalState (name := .indexed "named_tuple_combiner" 1) :=
      Silean.Modules.NamedTupleCombiner.designWith
      stateMap ControlState.schema,
    ordinaryState (name := .indexed "named_tuple_combiner" 2) :=
      Silean.Modules.NamedTupleCombiner.designWith
      stateMap ControlState.schema,
    decodedState (name := .indexed "mux" 0) :=
      Silean.Modules.Mux.design stateType,
    finalState (name := .indexed "mux" 1) :=
      Silean.Modules.Mux.design stateType,
    result (name := .indexed "named_tuple_combiner" 3) :=
      Silean.Modules.NamedTupleCombiner.designWith
      TransitionValue.signalMap TransitionValue.schema }
  wiring {
  outputs { .transition := result.value }
  instance (.inputsFields) { .value := input.inputs }
  instance (.currentFields) { .value := input.current }
  instance (.updatedFields) { .value := input.updated }
  instance (.falseBit) {}
  instance (.trueBit) {}
  instance (.wordSize) {}
  instance (.loadRs1State) {}
  instance (.notDecoder) { .input := currentFields[.decoder_trigger] }
  instance (.notJalr) { .input := inputsFields[.instr_jalr] }
  instance (.commonState) {
    .cpu_state := updatedFields[.cpu_state],
    .latched_store := falseBit.output,
    .latched_stalu := falseBit.output,
    .latched_branch := falseBit.output,
    .latched_is_lu := falseBit.output,
    .latched_is_lh := falseBit.output,
    .latched_is_lb := falseBit.output,
    .latched_rd := inputsFields[.decoded_rd],
    .mem_wordsize := wordSize.output,
    .mem_do_prefetch := updatedFields[.mem_do_prefetch],
    .mem_do_rinst := notDecoder.output,
    .mem_do_rdata := updatedFields[.mem_do_rdata],
    .mem_do_wdata := updatedFields[.mem_do_wdata],
    .decoder_trigger := updatedFields[.decoder_trigger],
    .decoder_pseudo_trigger := updatedFields[.decoder_pseudo_trigger],
    .trap := updatedFields[.trap] }
  instance (.commonFields) { .value := commonState.value }
  instance (.jalState) {
    .cpu_state := commonFields[.cpu_state],
    .latched_store := commonFields[.latched_store],
    .latched_stalu := commonFields[.latched_stalu],
    .latched_branch := trueBit.output,
    .latched_is_lu := commonFields[.latched_is_lu],
    .latched_is_lh := commonFields[.latched_is_lh],
    .latched_is_lb := commonFields[.latched_is_lb],
    .latched_rd := commonFields[.latched_rd],
    .mem_wordsize := commonFields[.mem_wordsize],
    .mem_do_prefetch := commonFields[.mem_do_prefetch],
    .mem_do_rinst := trueBit.output,
    .mem_do_rdata := commonFields[.mem_do_rdata],
    .mem_do_wdata := commonFields[.mem_do_wdata],
    .decoder_trigger := commonFields[.decoder_trigger],
    .decoder_pseudo_trigger := commonFields[.decoder_pseudo_trigger],
    .trap := commonFields[.trap] }
  instance (.ordinaryState) {
    .cpu_state := loadRs1State.output,
    .latched_store := commonFields[.latched_store],
    .latched_stalu := commonFields[.latched_stalu],
    .latched_branch := commonFields[.latched_branch],
    .latched_is_lu := commonFields[.latched_is_lu],
    .latched_is_lh := commonFields[.latched_is_lh],
    .latched_is_lb := commonFields[.latched_is_lb],
    .latched_rd := commonFields[.latched_rd],
    .mem_wordsize := commonFields[.mem_wordsize],
    .mem_do_prefetch := notJalr.output,
    .mem_do_rinst := falseBit.output,
    .mem_do_rdata := commonFields[.mem_do_rdata],
    .mem_do_wdata := commonFields[.mem_do_wdata],
    .decoder_trigger := commonFields[.decoder_trigger],
    .decoder_pseudo_trigger := commonFields[.decoder_pseudo_trigger],
    .trap := commonFields[.trap] }
  instance (.decodedState) {
    .select := inputsFields[.instr_jal],
    .whenFalse := ordinaryState.value,
    .whenTrue := jalState.value }
  instance (.finalState) {
    .select := notDecoder.output,
    .whenFalse := decodedState.result,
    .whenTrue := commonState.value }
  instance (.result) {
    .state := finalState.result,
    .setRinst := falseBit.output,
    .setRdata := falseBit.output,
    .setWdata := falseBit.output }
  }

end PicoRV.Control
