import Silean.Examples.PicoRV.Memory.MemoryLookahead
import Silean.Examples.PicoRV.Memory.MemoryNext
import Silean.Examples.PicoRV.Memory.MemoryReadFormatting
import Silean.Examples.PicoRV.Memory.MemoryResponse
import Silean.Authoring.ModuleDesign
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Modules.Register.Register

namespace Silean.Examples.PicoRV

open Silean
open Silean.Authoring

/-! The complete memory interface stores the seven source-owned registers in
one aggregate register. Its current tuple feeds the public registered outputs
and three combinational views: look-ahead request generation, load-data
formatting, and completion/response bypass. `Memory.Next` computes the tuple
captured on the next edge. -/
module_design Memory (name := "PicoRVMemory") where
  boundary (Memory.ports) (naming := Memory.Naming.ports)
  instances {
    inputsValue := Modules.NamedTupleCombiner.designWith
      Memory.MemoryInputs.signalMap Memory.MemoryInputs.schema,
    storage := Modules.Register.designWith Memory.MemoryState.schema,
    stateFields := Modules.NamedTupleSplitter.designWith
      Memory.stateMap Memory.MemoryState.schema,
    lookahead := Memory.Lookahead.design,
    readFormatting := Memory.ReadFormatting.design,
    response := Memory.Response.design,
    next := Memory.Next.design }
  wiring {
  outputs {
    .mem_valid := stateFields[.mem_valid],
    .mem_instr := stateFields[.mem_instr],
    .mem_addr := stateFields[.mem_addr],
    .mem_wdata := stateFields[.mem_wdata],
    .mem_wstrb := stateFields[.mem_wstrb],
    .mem_la_read := lookahead.mem_la_read,
    .mem_la_write := lookahead.mem_la_write,
    .mem_la_addr := lookahead.mem_la_addr,
    .mem_la_wdata := lookahead.mem_la_wdata,
    .mem_la_wstrb := lookahead.mem_la_wstrb,
    .mem_done := response.mem_done,
    .mem_rdata_word := readFormatting.mem_rdata_word,
    .mem_rdata_latched := response.mem_rdata_latched,
    .mem_rdata_q := stateFields[.mem_rdata_q] }
  instance (.inputsValue) {
    .resetn := input.resetn,
    .trap := input.trap,
    .mem_do_prefetch := input.mem_do_prefetch,
    .mem_do_rinst := input.mem_do_rinst,
    .mem_do_rdata := input.mem_do_rdata,
    .mem_do_wdata := input.mem_do_wdata,
    .next_pc := input.next_pc,
    .reg_op1 := input.reg_op1,
    .reg_op2 := input.reg_op2,
    .mem_wordsize := input.mem_wordsize,
    .mem_ready := input.mem_ready,
    .mem_rdata := input.mem_rdata }
  instance (.storage) { .input := next.state }
  instance (.stateFields) { .value := storage.output }
  instance (.lookahead) {
    .resetn := input.resetn,
    .mem_do_prefetch := input.mem_do_prefetch,
    .mem_do_rinst := input.mem_do_rinst,
    .mem_do_rdata := input.mem_do_rdata,
    .mem_do_wdata := input.mem_do_wdata,
    .next_pc := input.next_pc,
    .reg_op1 := input.reg_op1,
    .reg_op2 := input.reg_op2,
    .mem_wordsize := input.mem_wordsize,
    .current := storage.output }
  instance (.readFormatting) {
    .mem_wordsize := input.mem_wordsize,
    .reg_op1 := input.reg_op1,
    .mem_rdata := input.mem_rdata }
  instance (.response) {
    .resetn := input.resetn,
    .mem_do_rinst := input.mem_do_rinst,
    .mem_do_rdata := input.mem_do_rdata,
    .mem_do_wdata := input.mem_do_wdata,
    .mem_ready := input.mem_ready,
    .mem_rdata := input.mem_rdata,
    .current := storage.output }
  instance (.next) {
    .inputs := inputsValue.value,
    .current := storage.output }
  }

end Silean.Examples.PicoRV
