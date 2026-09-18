import PicoRV.Memory.MemoryCombinationalContracts
import PicoRV.Memory.MemoryLookahead
import PicoRV.Memory.MemoryNextContracts
import Silean.Authoring.ModuleDesign
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.Mux
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Primitives.Or

namespace PicoRV.Memory

open Silean
open Silean.Authoring

/-! Captures the look-ahead request fields before the phase-specific state
update. The `Lookahead` child is substituted by its concrete certification once
its formatting hierarchy is complete. -/
module_design LookaheadCapture (name := "picorv32_memory_lookahead_capture") where
  boundary (StateUpdate.ports) (naming := StateUpdate.Naming.ports)
  instances {
    inputsFields := Silean.Modules.NamedTupleSplitter.designWith
      MemoryInputs.signalMap MemoryInputs.schema,
    updatedFields := Silean.Modules.NamedTupleSplitter.designWith
      stateMap MemoryState.schema,
    lookahead := Lookahead.design,
    active := Silean.Primitives.orDesign,
    zeroMask := Silean.Modules.Constant.design (.vector 4 .bit) (maskOfNat 0),
    writeMask := Silean.Modules.Mux.design (.vector 4 .bit),
    address := Silean.Modules.Mux.design (.vector 32 .bit),
    mask := Silean.Modules.Mux.design (.vector 4 .bit),
    writeData := Silean.Modules.Mux.design (.vector 32 .bit),
    result := Silean.Modules.NamedTupleCombiner.designWith
      stateMap MemoryState.schema }
  wiring {
  outputs { .state := result.value }
  instance (.inputsFields) { .value := input.inputs }
  instance (.updatedFields) { .value := input.updated }
  instance (.lookahead) {
    .resetn := inputsFields[.resetn],
    .mem_do_prefetch := inputsFields[.mem_do_prefetch],
    .mem_do_rinst := inputsFields[.mem_do_rinst],
    .mem_do_rdata := inputsFields[.mem_do_rdata],
    .mem_do_wdata := inputsFields[.mem_do_wdata],
    .next_pc := inputsFields[.next_pc],
    .reg_op1 := inputsFields[.reg_op1],
    .reg_op2 := inputsFields[.reg_op2],
    .mem_wordsize := inputsFields[.mem_wordsize],
    .current := input.current }
  instance (.active) {
    .left := lookahead.mem_la_read,
    .right := lookahead.mem_la_write }
  instance (.zeroMask) {}
  instance (.writeMask) {
    .select := lookahead.mem_la_write,
    .whenFalse := zeroMask.output,
    .whenTrue := lookahead.mem_la_wstrb }
  instance (.address) {
    .select := active.output,
    .whenFalse := updatedFields[.mem_addr],
    .whenTrue := lookahead.mem_la_addr }
  instance (.mask) {
    .select := active.output,
    .whenFalse := updatedFields[.mem_wstrb],
    .whenTrue := writeMask.result }
  instance (.writeData) {
    .select := lookahead.mem_la_write,
    .whenFalse := updatedFields[.mem_wdata],
    .whenTrue := lookahead.mem_la_wdata }
  instance (.result) {
    .mem_state := updatedFields[.mem_state],
    .mem_valid := updatedFields[.mem_valid],
    .mem_instr := updatedFields[.mem_instr],
    .mem_addr := address.result,
    .mem_wdata := writeData.result,
    .mem_wstrb := mask.result,
    .mem_rdata_q := updatedFields[.mem_rdata_q] }
  }

end PicoRV.Memory
