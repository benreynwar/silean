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

/-! Load transition hardware. `latched_store` is set even while a prefetch
causes the phase to wait. Outside that wait, request start captures size and
signedness metadata, while completion independently returns to fetch and
raises both decoder triggers. -/

module_design LoadTransition (name := "picorv32_control_load_transition") where
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
    notRdata := Silean.Primitives.notDesign,
    byteLoad := Silean.Primitives.orDesign,
    halfLoad := Silean.Primitives.orDesign,
    halfOrWord := Silean.Modules.Mux.design (.vector 2 .bit),
    loadSize := Silean.Modules.Mux.design (.vector 2 .bit),
    capturedWordsize := Silean.Modules.Mux.design (.vector 2 .bit),
    capturedUnsigned := Silean.Modules.BitMux.design,
    capturedHalf := Silean.Modules.BitMux.design,
    capturedByte := Silean.Modules.BitMux.design,
    notPrefetch := Silean.Primitives.notDesign,
    finish := Silean.Primitives.andDesign,
    finishedPhase := Silean.Modules.Mux.design (.vector 8 .bit),
    finishedDecoder := Silean.Modules.BitMux.design,
    finishedPseudo := Silean.Modules.BitMux.design,
    activeState := Silean.Modules.NamedTupleCombiner.designWith
      stateMap ControlState.schema,
    activeTransition := Silean.Modules.NamedTupleCombiner.designWith
      TransitionValue.signalMap TransitionValue.schema,
    waitState := Silean.Modules.NamedTupleCombiner.designWith
      stateMap ControlState.schema,
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
  instance (.notRdata) { .input := currentFields[.mem_do_rdata] }
  instance (.byteLoad) {
    .left := inputsFields[.instr_lb], .right := inputsFields[.instr_lbu] }
  instance (.halfLoad) {
    .left := inputsFields[.instr_lh], .right := inputsFields[.instr_lhu] }
  instance (.halfOrWord) {
    .select := halfLoad.output,
    .whenFalse := sizeWord.output,
    .whenTrue := sizeHalf.output }
  instance (.loadSize) {
    .select := byteLoad.output,
    .whenFalse := halfOrWord.result,
    .whenTrue := sizeByte.output }
  instance (.capturedWordsize) {
    .select := notRdata.output,
    .whenFalse := updatedFields[.mem_wordsize],
    .whenTrue := loadSize.result }
  instance (.capturedUnsigned) {
    .select := notRdata.output,
    .whenFalse := updatedFields[.latched_is_lu],
    .whenTrue := inputsFields[.is_lbu_lhu_lw] }
  instance (.capturedHalf) {
    .select := notRdata.output,
    .whenFalse := updatedFields[.latched_is_lh],
    .whenTrue := inputsFields[.instr_lh] }
  instance (.capturedByte) {
    .select := notRdata.output,
    .whenFalse := updatedFields[.latched_is_lb],
    .whenTrue := inputsFields[.instr_lb] }
  instance (.notPrefetch) { .input := currentFields[.mem_do_prefetch] }
  instance (.finish) {
    .left := notPrefetch.output, .right := inputsFields[.mem_done] }
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
    .latched_store := trueBit.output,
    .latched_stalu := updatedFields[.latched_stalu],
    .latched_branch := updatedFields[.latched_branch],
    .latched_is_lu := capturedUnsigned.result,
    .latched_is_lh := capturedHalf.result,
    .latched_is_lb := capturedByte.result,
    .latched_rd := updatedFields[.latched_rd],
    .mem_wordsize := capturedWordsize.result,
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
    .setRdata := notRdata.output,
    .setWdata := falseBit.output }
  instance (.waitState) {
    .cpu_state := updatedFields[.cpu_state],
    .latched_store := trueBit.output,
    .latched_stalu := updatedFields[.latched_stalu],
    .latched_branch := updatedFields[.latched_branch],
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
  instance (.waitTransition) {
    .state := waitState.value,
    .setRinst := falseBit.output,
    .setRdata := falseBit.output,
    .setWdata := falseBit.output }
  instance (.result) {
    .select := waitForPrefetch.output,
    .whenFalse := activeTransition.value,
    .whenTrue := waitTransition.value }
  }

end PicoRV.Control
