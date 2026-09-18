import Silean.Examples.PicoRV.Memory.MemoryBasicUpdates
import Silean.Examples.PicoRV.Memory.MemoryLookaheadCapture
import Silean.Authoring.ModuleDesign
import Silean.Modules.Mux.Mux
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter

namespace Silean.Examples.PicoRV.Memory

open Silean
open Silean.Authoring

/-! Complete combinational memory transition. Response capture is computed
first, then look-ahead field capture, then the phase update. The final
reset/trap child selects from the response-captured baseline so a simultaneous
transfer is retained exactly as in the source's separate clocked process. -/
module_design Next (name := "picorv32_memory_next") where
  boundary (Next.ports) (naming := Next.Naming.ports)
  instances {
    currentFields := Modules.NamedTupleSplitter.designWith
      stateMap MemoryState.schema,
    responseCapture := ResponseCapture.design,
    lookaheadCapture := LookaheadCapture.design,
    phaseDecode := PhaseDecode.design,
    idle := IdleUpdate.design,
    read := ReadUpdate.design,
    write := WriteUpdate.design,
    prefetched := PrefetchedUpdate.design,
    selectWrite := Modules.Mux.design stateType,
    selectRead := Modules.Mux.design stateType,
    selectIdle := Modules.Mux.design stateType,
    resetTrapOverride := ResetTrapOverride.design }
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

end Silean.Examples.PicoRV.Memory
