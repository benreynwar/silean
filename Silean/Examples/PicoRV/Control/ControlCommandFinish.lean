import Silean.Examples.PicoRV.Control
import Silean.Authoring.ModuleDesign
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Naming.PrimitiveNaming

namespace Silean.Examples.PicoRV.Control.CommandFinish

open Silean
open Silean.Authoring

/-! The final command-priority layer from PicoRV32's sequential control block.
It receives a complete proposed transition. When `clear` is high it first
clears all four memory commands, then reasserts the three commands represented
by blocking `set_mem_do_*` intents. All non-command state fields pass through
unchanged.

Keeping this as a separate combinational module makes the source assignment
order explicit and gives the parent Control proof a natural semantic boundary:
the result is exactly `Control.finishCommands`. -/

module_ports ports where
  input clear : .bit,
  input transition (schema := TransitionValue.schema) : transitionType,
  output state (schema := ControlState.schema) : stateType

def outputState (inputs : inputMap.Values) : stateMap.Values :=
  finishCommands (inputs .clear) (Transition.unpack (inputs .transition))

def outputValues (inputs : inputMap.Values) : outputMap.Values
  | .state => stateMap.pack (outputState inputs)

def outputRule : Contracts.Cycle.CycleOutputRule ports emptySignalMap where
  readsInputs := .all inputMap
  writesOutputs := .all outputMap
  target inputs _ := outputValues inputs

module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule apply := outputRule
  state_rule := Contracts.Cycle.CycleStateRule.empty _

@[simp] theorem outputRule_holds_iff
    (inputs : inputMap.Values) (state : emptySignalMap.Values)
    (outputs : outputMap.Values) :
    outputRule.Holds inputs state outputs ↔
      outputs .state = stateMap.pack (outputState inputs) := by
  simp only [Contracts.Cycle.CycleOutputRule.Holds, outputRule,
    SignalGroup.all_matches]
  constructor
  · intro equal
    exact congrFun equal .state
  · intro equal
    funext output
    cases output
    exact equal

theorem state_of_evaluatesTo
    (inputs : inputMap.Values) (state : emptySignalMap.Values)
    (outputs : outputMap.Values) (nextState : emptySignalMap.Values)
    (evaluates : cycleContract.EvaluatesTo inputs state outputs nextState) :
    stateMap.unpack (outputs .state) =
      finishCommands (inputs .clear) (Transition.unpack (inputs .transition)) := by
  have packed := (outputRule_holds_iff inputs state outputs).mp
    (evaluates.1 Rule.apply)
  rw [packed, stateMap.unpack_pack]
  rfl

end Silean.Examples.PicoRV.Control.CommandFinish

namespace Silean.Examples.PicoRV.Control

open Silean
open Silean.Authoring

/-! ## Hardware structure

The two splitters expose the transition and its proposed state. Four AND gates
retain existing commands only when clearing is disabled. Three OR gates then
apply the set-command intents. The final named-tuple combiner passes every
other state field through unchanged. -/

module_design CommandFinish (name := "picorv32_control_command_finish") where
  boundary (CommandFinish.ports) (naming := CommandFinish.Naming.ports)
  instances {
    transitionFields := Modules.NamedTupleSplitter.designWith
      TransitionValue.signalMap TransitionValue.schema,
    stateFields := Modules.NamedTupleSplitter.designWith stateMap ControlState.schema,
    notClear := Primitives.notDesign,
    keepPrefetch := Primitives.andDesign,
    keepRinst := Primitives.andDesign,
    keepRdata := Primitives.andDesign,
    keepWdata := Primitives.andDesign,
    finishRinst := Primitives.orDesign,
    finishRdata := Primitives.orDesign,
    finishWdata := Primitives.orDesign,
    result := Modules.NamedTupleCombiner.designWith stateMap ControlState.schema }
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

end Silean.Examples.PicoRV.Control
