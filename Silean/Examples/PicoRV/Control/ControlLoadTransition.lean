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

/-! Load transition hardware. `latched_store` is set even while a prefetch
causes the phase to wait. Outside that wait, request start captures size and
signedness metadata, while completion independently returns to fetch and
raises both decoder triggers. -/

module_design LoadTransition (name := "picorv32_control_load_transition") where
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
    notRdata := Primitives.notDesign,
    byteLoad := Primitives.orDesign,
    halfLoad := Primitives.orDesign,
    halfOrWord := Modules.Mux.design (.vector 2 .bit),
    loadSize := Modules.Mux.design (.vector 2 .bit),
    capturedWordsize := Modules.Mux.design (.vector 2 .bit),
    capturedUnsigned := Modules.BitMux.design,
    capturedHalf := Modules.BitMux.design,
    capturedByte := Modules.BitMux.design,
    notPrefetch := Primitives.notDesign,
    finish := Primitives.andDesign,
    finishedPhase := Modules.Mux.design (.vector 8 .bit),
    finishedDecoder := Modules.BitMux.design,
    finishedPseudo := Modules.BitMux.design,
    activeState := Modules.NamedTupleCombiner.designWith
      stateMap ControlState.schema,
    activeTransition := Modules.NamedTupleCombiner.designWith
      TransitionValue.signalMap TransitionValue.schema,
    waitState := Modules.NamedTupleCombiner.designWith
      stateMap ControlState.schema,
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

end Silean.Examples.PicoRV.Control
