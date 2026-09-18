import Silean.Examples.PicoRV.Control.ControlBaseline
import Silean.Examples.PicoRV.Control.ControlCommandFinish
import Silean.Examples.PicoRV.Control.ControlExecuteTransition
import Silean.Examples.PicoRV.Control.ControlFetchTransition
import Silean.Examples.PicoRV.Control.ControlLoadTransition
import Silean.Examples.PicoRV.Control.ControlLoadRs1Transition
import Silean.Examples.PicoRV.Control.ControlLoadRs2Transition
import Silean.Examples.PicoRV.Control.ControlPhaseDecode
import Silean.Examples.PicoRV.Control.ControlResetAndAlignmentOverride
import Silean.Examples.PicoRV.Control.ControlStoreTransition
import Silean.Examples.PicoRV.Control.ControlShiftTransition
import Silean.Examples.PicoRV.Control.ControlTrapTransition
import Silean.Authoring.ModuleDesign
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.Mux
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Naming.PrimitiveNaming

namespace Silean.Examples.PicoRV.Control

open Silean
open Silean.Authoring

/-! Structural assembly of one complete control-state update. The hierarchy
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
    inputsFields := Modules.NamedTupleSplitter.designWith
      ControlInputs.signalMap ControlInputs.schema,
    currentFields := Modules.NamedTupleSplitter.designWith
      stateMap ControlState.schema,
    falseBit := Modules.Constant.design .bit false,
    baseline := Baseline.design,
    phaseDecode := PhaseDecode.design,
    trap := TrapTransition.design,
    fetch := FetchTransition.design,
    loadRs1 := LoadRs1Transition.design,
    loadRs2 := LoadRs2Transition.design,
    execute := ExecuteTransition.design,
    shift := ShiftTransition.design,
    store := StoreTransition.design,
    load := LoadTransition.design,
    defaultTransition := Modules.NamedTupleCombiner.designWith
      TransitionValue.signalMap TransitionValue.schema,
    selectLoad := Modules.Mux.designWith transitionType TransitionValue.schema,
    selectStore := Modules.Mux.designWith transitionType TransitionValue.schema,
    selectShift := Modules.Mux.designWith transitionType TransitionValue.schema,
    selectExecute := Modules.Mux.designWith transitionType TransitionValue.schema,
    selectLoadRs2 := Modules.Mux.designWith transitionType TransitionValue.schema,
    selectLoadRs1 := Modules.Mux.designWith transitionType TransitionValue.schema,
    selectFetch := Modules.Mux.designWith transitionType TransitionValue.schema,
    selectTrap := Modules.Mux.designWith transitionType TransitionValue.schema,
    override := ResetAndAlignmentOverride.design,
    notResetn := Primitives.notDesign,
    clearCommands := Primitives.orDesign,
    commandFinish := CommandFinish.design }
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

end Silean.Examples.PicoRV.Control
