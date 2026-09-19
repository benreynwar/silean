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

/-! Expanded typed production structure corresponding to the concise Store
transition definition in `ControlStoreTransition.lean`. -/

module_design StoreTransition (name := "picorv32_control_store_transition") where
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
    sizeWord (name := .indexed "constant" 2) :=
      Silean.Modules.Constant.design (.vector 2 .bit) (twoBitsOfNat 0),
    sizeHalf (name := .indexed "constant" 3) :=
      Silean.Modules.Constant.design (.vector 2 .bit) (twoBitsOfNat 1),
    sizeByte (name := .indexed "constant" 4) :=
      Silean.Modules.Constant.design (.vector 2 .bit) (twoBitsOfNat 2),
    fetchState (name := .indexed "constant" 5) :=
      Silean.Modules.Constant.design (.vector 8 .bit)
      (stateBits cpuStateFetch),
    notDone (name := .indexed "not" 0) := Silean.Primitives.notDesign,
    waitForPrefetch (name := .indexed "and" 0) := Silean.Primitives.andDesign,
    notWdata (name := .indexed "not" 1) := Silean.Primitives.notDesign,
    halfOrWord (name := .indexed "mux" 0) :=
      Silean.Modules.Mux.design (.vector 2 .bit),
    storeSize (name := .indexed "mux" 1) :=
      Silean.Modules.Mux.design (.vector 2 .bit),
    startedWordsize (name := .indexed "mux" 2) :=
      Silean.Modules.Mux.design (.vector 2 .bit),
    notPrefetch (name := .indexed "not" 2) := Silean.Primitives.notDesign,
    finish (name := .indexed "and" 1) := Silean.Primitives.andDesign,
    finishedPhase (name := .indexed "mux" 3) :=
      Silean.Modules.Mux.design (.vector 8 .bit),
    finishedDecoder (name := .indexed "bit_mux" 0) := Silean.Modules.BitMux.design,
    finishedPseudo (name := .indexed "bit_mux" 1) := Silean.Modules.BitMux.design,
    activeState (name := .indexed "named_tuple_combiner" 0) :=
      Silean.Modules.NamedTupleCombiner.designWith
      stateMap ControlState.schema,
    activeTransition (name := .indexed "named_tuple_combiner" 1) :=
      Silean.Modules.NamedTupleCombiner.designWith
      TransitionValue.signalMap TransitionValue.schema,
    waitTransition (name := .indexed "named_tuple_combiner" 2) :=
      Silean.Modules.NamedTupleCombiner.designWith
      TransitionValue.signalMap TransitionValue.schema,
    result (name := .indexed "mux" 4) :=
      Silean.Modules.Mux.design transitionType }
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
