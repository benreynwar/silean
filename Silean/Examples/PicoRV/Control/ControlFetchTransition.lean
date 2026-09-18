import Silean.Examples.PicoRV.Control.ControlNextContracts
import Silean.Authoring.ModuleDesign
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.Mux
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Naming.PrimitiveNaming

namespace Silean.Examples.PicoRV.Control

open Silean
open Silean.Authoring

/-! Fetch deliberately reads the pre-edge `decoder_trigger`. The common state
captures the destination register and clears transient metadata. An absent
decode requests an instruction and stays in fetch. A present decode selects
JAL (reissue instruction read and mark a branch) or the ordinary/JALR path
(enter load-RS1 and enable prefetch except for JALR). -/

module_design FetchTransition (name := "picorv32_control_fetch_transition") where
  boundary (PhaseTransition.ports) (naming := PhaseTransition.Naming.ports)
  instances {
    inputsFields := Modules.NamedTupleSplitter.designWith
      ControlInputs.signalMap ControlInputs.schema,
    currentFields := Modules.NamedTupleSplitter.designWith
      stateMap ControlState.schema,
    updatedFields := Modules.NamedTupleSplitter.designWith
      stateMap ControlState.schema,
    falseBit := Modules.Constant.design .bit false,
    trueBit := Modules.Constant.design .bit true,
    wordSize := Modules.Constant.design (.vector 2 .bit) (twoBitsOfNat 0),
    loadRs1State := Modules.Constant.design (.vector 8 .bit)
      (stateBits cpuStateLdRs1),
    notDecoder := Primitives.notDesign,
    notJalr := Primitives.notDesign,
    commonState := Modules.NamedTupleCombiner.designWith
      stateMap ControlState.schema,
    commonFields := Modules.NamedTupleSplitter.designWith
      stateMap ControlState.schema,
    jalState := Modules.NamedTupleCombiner.designWith
      stateMap ControlState.schema,
    ordinaryState := Modules.NamedTupleCombiner.designWith
      stateMap ControlState.schema,
    decodedState := Modules.Mux.designWith stateType ControlState.schema,
    finalState := Modules.Mux.designWith stateType ControlState.schema,
    result := Modules.NamedTupleCombiner.designWith
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

end Silean.Examples.PicoRV.Control
