import Silean.Examples.PicoRV.Control.ControlNextContracts
import Silean.Authoring.ModuleDesign
import Silean.Modules.EqualsConstant.EqualsConstant

namespace Silean.Examples.PicoRV.Control

open Silean
open Silean.Authoring

/-! Exact full-vector phase decoding. The eight comparisons are independent;
no one-hot or reachability assumption is built into the circuit. -/

module_design PhaseDecode (name := "picorv32_control_phase_decode") where
  boundary (PhaseDecode.ports) (naming := PhaseDecode.Naming.ports)
  instances {
    trap (name := "trapMatch") := Modules.EqualsConstant.design (.vector 8 .bit)
      (stateBits cpuStateTrap),
    fetch (name := "fetchMatch") := Modules.EqualsConstant.design (.vector 8 .bit)
      (stateBits cpuStateFetch),
    loadRs1 (name := "loadRs1Match") := Modules.EqualsConstant.design (.vector 8 .bit)
      (stateBits cpuStateLdRs1),
    loadRs2 (name := "loadRs2Match") := Modules.EqualsConstant.design (.vector 8 .bit)
      (stateBits cpuStateLdRs2),
    execute (name := "executeMatch") := Modules.EqualsConstant.design (.vector 8 .bit)
      (stateBits cpuStateExec),
    shift (name := "shiftMatch") := Modules.EqualsConstant.design (.vector 8 .bit)
      (stateBits cpuStateShift),
    store (name := "storeMatch") := Modules.EqualsConstant.design (.vector 8 .bit)
      (stateBits cpuStateStmem),
    load (name := "loadMatch") := Modules.EqualsConstant.design (.vector 8 .bit)
      (stateBits cpuStateLdmem) }
  wiring {
  outputs {
    .trap := trap.result,
    .fetch := fetch.result,
    .loadRs1 := loadRs1.result,
    .loadRs2 := loadRs2.result,
    .execute := execute.result,
    .shift := shift.result,
    .store := store.result,
    .load := load.result }
  instance (.trap) { .value := input.cpu_state }
  instance (.fetch) { .value := input.cpu_state }
  instance (.loadRs1) { .value := input.cpu_state }
  instance (.loadRs2) { .value := input.cpu_state }
  instance (.execute) { .value := input.cpu_state }
  instance (.shift) { .value := input.cpu_state }
  instance (.store) { .value := input.cpu_state }
  instance (.load) { .value := input.cpu_state }
  }

end Silean.Examples.PicoRV.Control
