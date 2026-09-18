import Silean.Examples.PicoRV.Control.ControlAlignment
import Silean.Authoring.ModuleDesign
import Silean.Modules.BitMux.BitMux
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.Mux
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Naming.PrimitiveNaming

namespace Silean.Examples.PicoRV.Control

open Silean
open Silean.Authoring

/-! This module makes the final two priority layers before command completion
visible. Reset first replaces the selected phase transition with a reset
transition derived from the baseline. Alignment is checked from the original
state and, when reset is inactive, overrides only the selected transition's
phase with `trap`; its command intents and all other proposed fields survive. -/

module_design ResetAndAlignmentOverride
    (name := "picorv32_control_reset_and_alignment_override") where
  boundary (ResetAndAlignmentOverride.ports)
    (naming := ResetAndAlignmentOverride.Naming.ports)
  instances {
    inputsFields := Modules.NamedTupleSplitter.designWith
      ControlInputs.signalMap ControlInputs.schema,
    baselineFields := Modules.NamedTupleSplitter.designWith
      stateMap ControlState.schema,
    falseBit := Modules.Constant.design .bit false,
    fetchState := Modules.Constant.design (.vector 8 .bit)
      (stateBits cpuStateFetch),
    trapState := Modules.Constant.design (.vector 8 .bit)
      (stateBits cpuStateTrap),
    resetState := Modules.NamedTupleCombiner.designWith
      stateMap ControlState.schema,
    resetTransition := Modules.NamedTupleCombiner.designWith
      TransitionValue.signalMap TransitionValue.schema,
    notResetn := Primitives.notDesign,
    resetSelection := Modules.Mux.designWith transitionType TransitionValue.schema,
    alignment := Alignment.design,
    anyMisalignment := Primitives.orDesign,
    alignmentEnabled := Primitives.andDesign,
    selectedTransitionFields := Modules.NamedTupleSplitter.designWith
      TransitionValue.signalMap TransitionValue.schema,
    selectedStateFields := Modules.NamedTupleSplitter.designWith
      stateMap ControlState.schema,
    alignmentState := Modules.NamedTupleCombiner.designWith
      stateMap ControlState.schema,
    alignmentTransition := Modules.NamedTupleCombiner.designWith
      TransitionValue.signalMap TransitionValue.schema,
    result := Modules.Mux.designWith transitionType TransitionValue.schema }
  wiring {
  outputs { .transition := result.result }
  instance (.inputsFields) { .value := input.inputs }
  instance (.baselineFields) { .value := input.baseline }
  instance (.falseBit) {}
  instance (.fetchState) {}
  instance (.trapState) {}
  instance (.resetState) {
    .cpu_state := fetchState.output,
    .latched_store := falseBit.output,
    .latched_stalu := falseBit.output,
    .latched_branch := falseBit.output,
    .latched_is_lu := falseBit.output,
    .latched_is_lh := falseBit.output,
    .latched_is_lb := falseBit.output,
    .latched_rd := baselineFields[.latched_rd],
    .mem_wordsize := baselineFields[.mem_wordsize],
    .mem_do_prefetch := baselineFields[.mem_do_prefetch],
    .mem_do_rinst := baselineFields[.mem_do_rinst],
    .mem_do_rdata := baselineFields[.mem_do_rdata],
    .mem_do_wdata := baselineFields[.mem_do_wdata],
    .decoder_trigger := baselineFields[.decoder_trigger],
    .decoder_pseudo_trigger := baselineFields[.decoder_pseudo_trigger],
    .trap := baselineFields[.trap] }
  instance (.resetTransition) {
    .state := resetState.value,
    .setRinst := falseBit.output,
    .setRdata := falseBit.output,
    .setWdata := falseBit.output }
  instance (.notResetn) { .input := inputsFields[.resetn] }
  instance (.resetSelection) {
    .select := notResetn.output,
    .whenFalse := input.selected,
    .whenTrue := resetTransition.value }
  instance (.alignment) {
    .inputs := input.inputs,
    .current := input.current }
  instance (.anyMisalignment) {
    .left := alignment.data,
    .right := alignment.instruction }
  instance (.alignmentEnabled) {
    .left := inputsFields[.resetn],
    .right := anyMisalignment.output }
  instance (.selectedTransitionFields) { .value := resetSelection.result }
  instance (.selectedStateFields) {
    .value := selectedTransitionFields[.state] }
  instance (.alignmentState) {
    .cpu_state := trapState.output,
    .latched_store := selectedStateFields[.latched_store],
    .latched_stalu := selectedStateFields[.latched_stalu],
    .latched_branch := selectedStateFields[.latched_branch],
    .latched_is_lu := selectedStateFields[.latched_is_lu],
    .latched_is_lh := selectedStateFields[.latched_is_lh],
    .latched_is_lb := selectedStateFields[.latched_is_lb],
    .latched_rd := selectedStateFields[.latched_rd],
    .mem_wordsize := selectedStateFields[.mem_wordsize],
    .mem_do_prefetch := selectedStateFields[.mem_do_prefetch],
    .mem_do_rinst := selectedStateFields[.mem_do_rinst],
    .mem_do_rdata := selectedStateFields[.mem_do_rdata],
    .mem_do_wdata := selectedStateFields[.mem_do_wdata],
    .decoder_trigger := selectedStateFields[.decoder_trigger],
    .decoder_pseudo_trigger := selectedStateFields[.decoder_pseudo_trigger],
    .trap := selectedStateFields[.trap] }
  instance (.alignmentTransition) {
    .state := alignmentState.value,
    .setRinst := selectedTransitionFields[.setRinst],
    .setRdata := selectedTransitionFields[.setRdata],
    .setWdata := selectedTransitionFields[.setWdata] }
  instance (.result) {
    .select := alignmentEnabled.output,
    .whenFalse := resetSelection.result,
    .whenTrue := alignmentTransition.value }
  }

end Silean.Examples.PicoRV.Control
