import PicoRV.Memory.MemoryCombinationalContracts
import Silean.Authoring.ModuleDesign
import Silean.Modules.EqualsConstant.EqualsConstant
import Silean.Modules.Mux.Mux
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Primitives.And
import Silean.Primitives.Not
import Silean.Primitives.Or

namespace PicoRV.Memory

open Silean
open Silean.Authoring

/-! Compute completion and the combinational response-data bypass. A normal
completion requires an accepted non-idle request and a live read/write
command. A prefetched instruction can instead complete later from phase 3,
without another memory transfer. -/
module_design Response (name := "picorv32_memory_response") where
  boundary (Response.ports) (naming := Response.Naming.ports)
  instances {
    currentFields := Silean.Modules.NamedTupleSplitter.designWith
      stateMap MemoryState.schema,
    transfer := Silean.Primitives.andDesign,
    idle := Silean.Modules.EqualsConstant.design (.vector 2 .bit) (stateOfNat 0),
    nonIdle := Silean.Primitives.notDesign,
    transferNonIdle := Silean.Primitives.andDesign,
    readCommand := Silean.Primitives.orDesign,
    activeCommand := Silean.Primitives.orDesign,
    ordinaryCompletion := Silean.Primitives.andDesign,
    prefetched := Silean.Modules.EqualsConstant.design (.vector 2 .bit) (stateOfNat 3),
    delayedCompletion := Silean.Primitives.andDesign,
    completion := Silean.Primitives.orDesign,
    enabledCompletion := Silean.Primitives.andDesign,
    responseData := Silean.Modules.Mux.design (.vector 32 .bit) }
  wiring {
  outputs {
    .mem_done := enabledCompletion.output,
    .mem_rdata_latched := responseData.result }
  instance (.currentFields) { .value := input.current }
  instance (.transfer) {
    .left := currentFields[.mem_valid],
    .right := input.mem_ready }
  instance (.idle) { .value := currentFields[.mem_state] }
  instance (.nonIdle) { .input := idle.result }
  instance (.transferNonIdle) {
    .left := transfer.output,
    .right := nonIdle.output }
  instance (.readCommand) {
    .left := input.mem_do_rinst,
    .right := input.mem_do_rdata }
  instance (.activeCommand) {
    .left := readCommand.output,
    .right := input.mem_do_wdata }
  instance (.ordinaryCompletion) {
    .left := transferNonIdle.output,
    .right := activeCommand.output }
  instance (.prefetched) { .value := currentFields[.mem_state] }
  instance (.delayedCompletion) {
    .left := prefetched.result,
    .right := input.mem_do_rinst }
  instance (.completion) {
    .left := ordinaryCompletion.output,
    .right := delayedCompletion.output }
  instance (.enabledCompletion) {
    .left := input.resetn,
    .right := completion.output }
  instance (.responseData) {
    .select := transfer.output,
    .whenFalse := currentFields[.mem_rdata_q],
    .whenTrue := input.mem_rdata }
  }

end PicoRV.Memory
