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

/-! Expanded typed production structure for the reader-facing response
definition in `MemoryResponse.lean`. -/
module_design Response (name := "picorv32_memory_response") where
  boundary (Response.ports) (naming := Response.Naming.ports)
  instances {
    currentFields (name := .indexed "named_tuple_splitter" 0) :=
      Silean.Modules.NamedTupleSplitter.designWith
      stateMap MemoryState.schema,
    transfer (name := .indexed "and" 0) := Silean.Primitives.andDesign,
    idle (name := .indexed "equals_constant" 0) :=
      Silean.Modules.EqualsConstant.design (.vector 2 .bit) (stateOfNat 0),
    nonIdle (name := .indexed "not" 0) := Silean.Primitives.notDesign,
    transferNonIdle (name := .indexed "and" 1) := Silean.Primitives.andDesign,
    readCommand (name := .indexed "or" 0) := Silean.Primitives.orDesign,
    activeCommand (name := .indexed "or" 1) := Silean.Primitives.orDesign,
    ordinaryCompletion (name := .indexed "and" 2) := Silean.Primitives.andDesign,
    prefetched (name := .indexed "equals_constant" 1) :=
      Silean.Modules.EqualsConstant.design (.vector 2 .bit) (stateOfNat 3),
    delayedCompletion (name := .indexed "and" 3) := Silean.Primitives.andDesign,
    completion (name := .indexed "or" 2) := Silean.Primitives.orDesign,
    enabledCompletion (name := .indexed "and" 4) := Silean.Primitives.andDesign,
    responseData (name := .indexed "mux" 0) :=
      Silean.Modules.Mux.design (.vector 32 .bit) }
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
