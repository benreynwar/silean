import PicoRV.Control.ControlBaseline
import PicoRV.Control.ControlCommandFinish
import PicoRV.Control.ControlExecuteTransition
import PicoRV.Control.ControlFetchTransition
import PicoRV.Control.ControlLoadTransition
import PicoRV.Control.ControlLoadRs1Transition
import PicoRV.Control.ControlLoadRs2Transition
import PicoRV.Control.ControlPhaseDecode
import PicoRV.Control.ControlResetAndAlignmentOverride
import PicoRV.Control.ControlStoreTransition
import PicoRV.Control.ControlShiftTransition
import PicoRV.Control.ControlTrapTransition
import Silean.Authoring.ModuleDesign
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.Mux
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Naming.PrimitiveNaming

namespace PicoRV.Control

open Silean
open Silean.Authoring

/-! Expanded structural assembly of one complete control-state update. The hierarchy
mirrors the source assignment order:

1. compute unconditional baseline assignments;
2. decode the old phase and select exactly one phase transition;
3. apply reset and alignment priorities;
4. clear completed commands and apply same-cycle command intents.

Every phase child is concrete. Their public contracts remain the source-level
transition functions, so this assembly depends on semantic behavior rather
than the children’s internal gate structure. -/

module_design ControlNext (name := "picorv32_control_next") where
  boundary (ControlNext.ports) (naming := ControlNext.Naming.ports)
  instances {
    inputsFields (name := .indexed "named_tuple_splitter" 0) :=
      Silean.Modules.NamedTupleSplitter.designWith
      ControlInputs.signalMap ControlInputs.schema,
    currentFields (name := .indexed "named_tuple_splitter" 1) :=
      Silean.Modules.NamedTupleSplitter.designWith
      stateMap ControlState.schema,
    falseBit (name := .indexed "constant" 0) :=
      Silean.Modules.Constant.design .bit false,
    baseline (name := .indexed "control_baseline" 0) := Baseline.design,
    phaseDecode (name := .indexed "control_phase_decode" 0) := PhaseDecode.design,
    trap (name := .indexed "trap_transition" 0) := TrapTransition.design,
    fetch (name := .indexed "fetch_transition" 0) := FetchTransition.design,
    loadRs1 (name := .indexed "load_rs1_transition" 0) :=
      LoadRs1Transition.design,
    loadRs2 (name := .indexed "load_rs2_transition" 0) :=
      LoadRs2Transition.design,
    execute (name := .indexed "execute_transition" 0) :=
      ExecuteTransition.design,
    shift (name := .indexed "shift_transition" 0) := ShiftTransition.design,
    store (name := .indexed "store_transition" 0) := StoreTransition.design,
    load (name := .indexed "load_transition" 0) := LoadTransition.design,
    defaultTransition (name := .indexed "named_tuple_combiner" 0) :=
      Silean.Modules.NamedTupleCombiner.designWith
      TransitionValue.signalMap TransitionValue.schema,
    selectLoad (name := .indexed "mux" 0) :=
      Silean.Modules.Mux.design transitionType,
    selectStore (name := .indexed "mux" 1) :=
      Silean.Modules.Mux.design transitionType,
    selectShift (name := .indexed "mux" 2) :=
      Silean.Modules.Mux.design transitionType,
    selectExecute (name := .indexed "mux" 3) :=
      Silean.Modules.Mux.design transitionType,
    selectLoadRs2 (name := .indexed "mux" 4) :=
      Silean.Modules.Mux.design transitionType,
    selectLoadRs1 (name := .indexed "mux" 5) :=
      Silean.Modules.Mux.design transitionType,
    selectFetch (name := .indexed "mux" 6) :=
      Silean.Modules.Mux.design transitionType,
    selectTrap (name := .indexed "mux" 7) :=
      Silean.Modules.Mux.design transitionType,
    override (name := .indexed "reset_alignment_override" 0) :=
      ResetAndAlignmentOverride.design,
    notResetn (name := .indexed "not" 0) := Silean.Primitives.notDesign,
    clearCommands (name := .indexed "or" 0) := Silean.Primitives.orDesign,
    commandFinish (name := .indexed "command_finish" 0) :=
      CommandFinish.design }
  wiring {
  outputs { .state := commandFinish.state }
  instance (.inputsFields) { .value := input.inputs }
  instance (.currentFields) { .value := input.current }
  instance (.falseBit) {}
  instance (.baseline) { .inputs := input.inputs, .current := input.current }
  instance (.phaseDecode) { .cpu_state := currentFields[.cpu_state] }
  instance (.trap) {
    .inputs := input.inputs, .current := input.current,
    .updated := baseline.state }
  instance (.fetch) {
    .inputs := input.inputs, .current := input.current,
    .updated := baseline.state }
  instance (.loadRs1) {
    .inputs := input.inputs, .current := input.current,
    .updated := baseline.state }
  instance (.loadRs2) {
    .inputs := input.inputs, .current := input.current,
    .updated := baseline.state }
  instance (.execute) {
    .inputs := input.inputs, .current := input.current,
    .updated := baseline.state }
  instance (.shift) {
    .inputs := input.inputs, .current := input.current,
    .updated := baseline.state }
  instance (.store) {
    .inputs := input.inputs, .current := input.current,
    .updated := baseline.state }
  instance (.load) {
    .inputs := input.inputs, .current := input.current,
    .updated := baseline.state }
  instance (.defaultTransition) {
    .state := baseline.state,
    .setRinst := falseBit.output,
    .setRdata := falseBit.output,
    .setWdata := falseBit.output }
  instance (.selectLoad) {
    .select := phaseDecode.load,
    .whenFalse := defaultTransition.value,
    .whenTrue := load.transition }
  instance (.selectStore) {
    .select := phaseDecode.store,
    .whenFalse := selectLoad.result,
    .whenTrue := store.transition }
  instance (.selectShift) {
    .select := phaseDecode.shift,
    .whenFalse := selectStore.result,
    .whenTrue := shift.transition }
  instance (.selectExecute) {
    .select := phaseDecode.execute,
    .whenFalse := selectShift.result,
    .whenTrue := execute.transition }
  instance (.selectLoadRs2) {
    .select := phaseDecode.loadRs2,
    .whenFalse := selectExecute.result,
    .whenTrue := loadRs2.transition }
  instance (.selectLoadRs1) {
    .select := phaseDecode.loadRs1,
    .whenFalse := selectLoadRs2.result,
    .whenTrue := loadRs1.transition }
  instance (.selectFetch) {
    .select := phaseDecode.fetch,
    .whenFalse := selectLoadRs1.result,
    .whenTrue := fetch.transition }
  instance (.selectTrap) {
    .select := phaseDecode.trap,
    .whenFalse := selectFetch.result,
    .whenTrue := trap.transition }
  instance (.override) {
    .inputs := input.inputs,
    .current := input.current,
    .baseline := baseline.state,
    .selected := selectTrap.result }
  instance (.notResetn) { .input := inputsFields[.resetn] }
  instance (.clearCommands) {
    .left := notResetn.output,
    .right := inputsFields[.mem_done] }
  instance (.commandFinish) {
    .clear := clearCommands.output,
    .transition := override.transition }
  }

end PicoRV.Control
