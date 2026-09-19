import PicoRV.ControlContract
import Silean.Authoring.ModuleDesign
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Naming.PrimitiveNaming

namespace PicoRV.Control

open Silean
open Silean.Authoring

/-! Expanded typed production structure corresponding to the concise authored
definition in `ControlCommandFinish.lean`. -/

module_design CommandFinish (name := "picorv32_control_command_finish") where
  ports {
    input clear : .bit,
    input transition (schema := TransitionValue.schema) : transitionType,
    output state (schema := ControlState.schema) : stateType }
  instances {
    transitionFields (name := .indexed "named_tuple_splitter" 0) :=
      Silean.Modules.NamedTupleSplitter.designWith
      TransitionValue.signalMap TransitionValue.schema,
    stateFields (name := .indexed "named_tuple_splitter" 1) :=
      Silean.Modules.NamedTupleSplitter.designWith stateMap ControlState.schema,
    notClear (name := .indexed "not" 0) := Silean.Primitives.notDesign,
    keepPrefetch (name := .indexed "and" 0) := Silean.Primitives.andDesign,
    keepRinst (name := .indexed "and" 1) := Silean.Primitives.andDesign,
    finishRinst (name := .indexed "or" 0) := Silean.Primitives.orDesign,
    keepRdata (name := .indexed "and" 2) := Silean.Primitives.andDesign,
    finishRdata (name := .indexed "or" 1) := Silean.Primitives.orDesign,
    keepWdata (name := .indexed "and" 3) := Silean.Primitives.andDesign,
    finishWdata (name := .indexed "or" 2) := Silean.Primitives.orDesign,
    result (name := .indexed "named_tuple_combiner" 0) :=
      Silean.Modules.NamedTupleCombiner.designWith stateMap ControlState.schema }
  wiring {
  outputs {
    .state := result.value }
  instance (.transitionFields) {
    .value := input.transition }
  instance (.stateFields) {
    .value := transitionFields[.state] }
  instance (.notClear) {
    .input := input.clear }
  instance (.keepPrefetch) {
    .left := stateFields[.mem_do_prefetch],
    .right := notClear.output }
  instance (.keepRinst) {
    .left := stateFields[.mem_do_rinst],
    .right := notClear.output }
  instance (.keepRdata) {
    .left := stateFields[.mem_do_rdata],
    .right := notClear.output }
  instance (.keepWdata) {
    .left := stateFields[.mem_do_wdata],
    .right := notClear.output }
  instance (.finishRinst) {
    .left := keepRinst.output,
    .right := transitionFields[.setRinst] }
  instance (.finishRdata) {
    .left := keepRdata.output,
    .right := transitionFields[.setRdata] }
  instance (.finishWdata) {
    .left := keepWdata.output,
    .right := transitionFields[.setWdata] }
  instance (.result) {
    .cpu_state := stateFields[.cpu_state],
    .latched_store := stateFields[.latched_store],
    .latched_stalu := stateFields[.latched_stalu],
    .latched_branch := stateFields[.latched_branch],
    .latched_is_lu := stateFields[.latched_is_lu],
    .latched_is_lh := stateFields[.latched_is_lh],
    .latched_is_lb := stateFields[.latched_is_lb],
    .latched_rd := stateFields[.latched_rd],
    .mem_wordsize := stateFields[.mem_wordsize],
    .mem_do_prefetch := keepPrefetch.output,
    .mem_do_rinst := finishRinst.output,
    .mem_do_rdata := finishRdata.output,
    .mem_do_wdata := finishWdata.output,
    .decoder_trigger := stateFields[.decoder_trigger],
    .decoder_pseudo_trigger := stateFields[.decoder_pseudo_trigger],
    .trap := stateFields[.trap] }
  }

end PicoRV.Control
