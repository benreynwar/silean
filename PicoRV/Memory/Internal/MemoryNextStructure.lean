import PicoRV.Memory.MemoryBasicUpdates
import PicoRV.Memory.MemoryLookaheadCapture
import Silean.Authoring.ModuleDesign
import Silean.Modules.Mux.Mux
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter

namespace PicoRV.Memory

open Silean
open Silean.Authoring

/-! Complete combinational memory transition. Response capture is computed
first, then look-ahead field capture, then the phase update. The final
reset/trap child selects from the response-captured baseline so a simultaneous
transfer is retained exactly as in the source's separate clocked process. -/
module_design Next (name := "picorv32_memory_next") where
  boundary (Next.ports) (naming := Next.Naming.ports)
  instances {
    currentFields (name := .indexed "named_tuple_splitter" 0) := Silean.Modules.NamedTupleSplitter.designWith
      stateMap MemoryState.schema,
    responseCapture (name := .indexed "memory_response_capture" 0) :=
      ResponseCapture.design,
    lookaheadCapture (name := .indexed "lookahead_capture" 0) :=
      LookaheadCapture.design,
    phaseDecode (name := .indexed "memory_phase_decode" 0) := PhaseDecode.design,
    idle (name := .indexed "memory_idle_update" 0) := IdleUpdate.design,
    read (name := .indexed "memory_read_update" 0) := ReadUpdate.design,
    write (name := .indexed "memory_write_update" 0) := WriteUpdate.design,
    prefetched (name := .indexed "memory_prefetched_update" 0) :=
      PrefetchedUpdate.design,
    selectWrite (name := .indexed "mux" 0) := Silean.Modules.Mux.design stateType,
    selectRead (name := .indexed "mux" 1) := Silean.Modules.Mux.design stateType,
    selectIdle (name := .indexed "mux" 2) := Silean.Modules.Mux.design stateType,
    resetTrapOverride (name := .indexed "memory_reset_trap_override" 0) :=
      ResetTrapOverride.design }
  wiring {
  outputs { .state := resetTrapOverride.state }
  instance (.currentFields) { .value := input.current }
  instance (.responseCapture) {
    .inputs := input.inputs,
    .current := input.current }
  instance (.lookaheadCapture) {
    .inputs := input.inputs,
    .current := input.current,
    .updated := responseCapture.state }
  instance (.phaseDecode) { .mem_state := currentFields[.mem_state] }
  instance (.idle) {
    .inputs := input.inputs,
    .current := input.current,
    .updated := lookaheadCapture.state }
  instance (.read) {
    .inputs := input.inputs,
    .current := input.current,
    .updated := lookaheadCapture.state }
  instance (.write) {
    .inputs := input.inputs,
    .current := input.current,
    .updated := lookaheadCapture.state }
  instance (.prefetched) {
    .inputs := input.inputs,
    .current := input.current,
    .updated := lookaheadCapture.state }
  instance (.selectWrite) {
    .select := phaseDecode.write,
    .whenFalse := prefetched.state,
    .whenTrue := write.state }
  instance (.selectRead) {
    .select := phaseDecode.read,
    .whenFalse := selectWrite.result,
    .whenTrue := read.state }
  instance (.selectIdle) {
    .select := phaseDecode.idle,
    .whenFalse := selectRead.result,
    .whenTrue := idle.state }
  instance (.resetTrapOverride) {
    .inputs := input.inputs,
    .captured := responseCapture.state,
    .normal := selectIdle.result }
  }

end PicoRV.Memory
