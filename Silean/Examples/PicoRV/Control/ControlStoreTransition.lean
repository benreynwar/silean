import Silean.Examples.PicoRV.Control.ControlNextContracts
import Silean.Authoring.ModuleDesign
import Silean.Modules.BitMux.BitMux
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.Mux
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Naming.PrimitiveNaming

namespace Silean.Examples.PicoRV.Control

open Silean
open Silean.Authoring

/-! Store transition hardware, preserving the source priority explicitly:
prefetch waiting selects an unchanged transition; otherwise request start may
capture size, completion may return to fetch, and `setWdata` records whether a
new write request must be asserted after command clearing. -/

module_design StoreTransition (name := "picorv32_control_store_transition") where
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
    sizeWord := Modules.Constant.design (.vector 2 .bit) (twoBitsOfNat 0),
    sizeHalf := Modules.Constant.design (.vector 2 .bit) (twoBitsOfNat 1),
    sizeByte := Modules.Constant.design (.vector 2 .bit) (twoBitsOfNat 2),
    fetchState := Modules.Constant.design (.vector 8 .bit)
      (stateBits cpuStateFetch),
    notDone := Primitives.notDesign,
    waitForPrefetch := Primitives.andDesign,
    notWdata := Primitives.notDesign,
    halfOrWord := Modules.Mux.design (.vector 2 .bit),
    storeSize := Modules.Mux.design (.vector 2 .bit),
    startedWordsize := Modules.Mux.design (.vector 2 .bit),
    notPrefetch := Primitives.notDesign,
    finish := Primitives.andDesign,
    finishedPhase := Modules.Mux.design (.vector 8 .bit),
    finishedDecoder := Modules.BitMux.design,
    finishedPseudo := Modules.BitMux.design,
    activeState := Modules.NamedTupleCombiner.designWith
      stateMap ControlState.schema,
    activeTransition := Modules.NamedTupleCombiner.designWith
      TransitionValue.signalMap TransitionValue.schema,
    waitTransition := Modules.NamedTupleCombiner.designWith
      TransitionValue.signalMap TransitionValue.schema,
    result := Modules.Mux.designWith transitionType TransitionValue.schema }
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

end Silean.Examples.PicoRV.Control
