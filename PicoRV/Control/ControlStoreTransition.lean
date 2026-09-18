import PicoRV.Control.ControlNextContracts
import Silean.Authoring.ModuleDesign
import Silean.Modules.BitMux.BitMux
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.Mux
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Naming.PrimitiveNaming

namespace PicoRV.Control

open Silean
open Silean.Authoring

/-! Store transition hardware, preserving the source priority explicitly:
prefetch waiting selects an unchanged transition; otherwise request start may
capture size, completion may return to fetch, and `setWdata` records whether a
new write request must be asserted after command clearing. -/

module_design StoreTransition (name := "picorv32_control_store_transition") where
  boundary (PhaseTransition.ports) (naming := PhaseTransition.Naming.ports)
  instances {
    inputsFields := Silean.Modules.NamedTupleSplitter.designWith
      ControlInputs.signalMap ControlInputs.schema,
    currentFields := Silean.Modules.NamedTupleSplitter.designWith
      stateMap ControlState.schema,
    updatedFields := Silean.Modules.NamedTupleSplitter.designWith
      stateMap ControlState.schema,
    falseBit := Silean.Modules.Constant.design .bit false,
    trueBit := Silean.Modules.Constant.design .bit true,
    sizeWord := Silean.Modules.Constant.design (.vector 2 .bit) (twoBitsOfNat 0),
    sizeHalf := Silean.Modules.Constant.design (.vector 2 .bit) (twoBitsOfNat 1),
    sizeByte := Silean.Modules.Constant.design (.vector 2 .bit) (twoBitsOfNat 2),
    fetchState := Silean.Modules.Constant.design (.vector 8 .bit)
      (stateBits cpuStateFetch),
    notDone := Silean.Primitives.notDesign,
    waitForPrefetch := Silean.Primitives.andDesign,
    notWdata := Silean.Primitives.notDesign,
    halfOrWord := Silean.Modules.Mux.design (.vector 2 .bit),
    storeSize := Silean.Modules.Mux.design (.vector 2 .bit),
    startedWordsize := Silean.Modules.Mux.design (.vector 2 .bit),
    notPrefetch := Silean.Primitives.notDesign,
    finish := Silean.Primitives.andDesign,
    finishedPhase := Silean.Modules.Mux.design (.vector 8 .bit),
    finishedDecoder := Silean.Modules.BitMux.design,
    finishedPseudo := Silean.Modules.BitMux.design,
    activeState := Silean.Modules.NamedTupleCombiner.designWith
      stateMap ControlState.schema,
    activeTransition := Silean.Modules.NamedTupleCombiner.designWith
      TransitionValue.signalMap TransitionValue.schema,
    waitTransition := Silean.Modules.NamedTupleCombiner.designWith
      TransitionValue.signalMap TransitionValue.schema,
    result := Silean.Modules.Mux.designWith transitionType TransitionValue.schema }
  wiring {
  outputs { .transition := result.result }
  instance (.inputsFields) { .value := input.inputs }
  instance (.currentFields) { .value := input.current }
  instance (.updatedFields) { .value := input.updated }
  instance (.falseBit) {}
  instance (.trueBit) {}
  instance (.sizeWord) {}
  instance (.sizeHalf) {}
  instance (.sizeByte) {}
  instance (.fetchState) {}
  instance (.notDone) { .input := inputsFields[.mem_done] }
  instance (.waitForPrefetch) {
    .left := currentFields[.mem_do_prefetch],
    .right := notDone.output }
  instance (.notWdata) { .input := currentFields[.mem_do_wdata] }
  instance (.halfOrWord) {
    .select := inputsFields[.instr_sh],
    .whenFalse := sizeWord.output,
    .whenTrue := sizeHalf.output }
  instance (.storeSize) {
    .select := inputsFields[.instr_sb],
    .whenFalse := halfOrWord.result,
    .whenTrue := sizeByte.output }
  instance (.startedWordsize) {
    .select := notWdata.output,
    .whenFalse := updatedFields[.mem_wordsize],
    .whenTrue := storeSize.result }
  instance (.notPrefetch) { .input := currentFields[.mem_do_prefetch] }
  instance (.finish) {
    .left := notPrefetch.output,
    .right := inputsFields[.mem_done] }
  instance (.finishedPhase) {
    .select := finish.output,
    .whenFalse := updatedFields[.cpu_state],
    .whenTrue := fetchState.output }
  instance (.finishedDecoder) {
    .select := finish.output,
    .whenFalse := updatedFields[.decoder_trigger],
    .whenTrue := trueBit.output }
  instance (.finishedPseudo) {
    .select := finish.output,
    .whenFalse := updatedFields[.decoder_pseudo_trigger],
    .whenTrue := trueBit.output }
  instance (.activeState) {
    .cpu_state := finishedPhase.result,
    .latched_store := updatedFields[.latched_store],
    .latched_stalu := updatedFields[.latched_stalu],
    .latched_branch := updatedFields[.latched_branch],
    .latched_is_lu := updatedFields[.latched_is_lu],
    .latched_is_lh := updatedFields[.latched_is_lh],
    .latched_is_lb := updatedFields[.latched_is_lb],
    .latched_rd := updatedFields[.latched_rd],
    .mem_wordsize := startedWordsize.result,
    .mem_do_prefetch := updatedFields[.mem_do_prefetch],
    .mem_do_rinst := updatedFields[.mem_do_rinst],
    .mem_do_rdata := updatedFields[.mem_do_rdata],
    .mem_do_wdata := updatedFields[.mem_do_wdata],
    .decoder_trigger := finishedDecoder.result,
    .decoder_pseudo_trigger := finishedPseudo.result,
    .trap := updatedFields[.trap] }
  instance (.activeTransition) {
    .state := activeState.value,
    .setRinst := falseBit.output,
    .setRdata := falseBit.output,
    .setWdata := notWdata.output }
  instance (.waitTransition) {
    .state := input.updated,
    .setRinst := falseBit.output,
    .setRdata := falseBit.output,
    .setWdata := falseBit.output }
  instance (.result) {
    .select := waitForPrefetch.output,
    .whenFalse := activeTransition.value,
    .whenTrue := waitTransition.value }
  }

end PicoRV.Control
