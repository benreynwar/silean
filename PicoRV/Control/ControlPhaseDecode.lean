import PicoRV.Control.ControlNextContracts
import PicoRV.Control.Internal.ControlPhaseDecodeStructure
import Silean.Authoring.CircuitDescription
import Silean.Modules.EqualsConstant.EqualsConstant

namespace PicoRV.Control

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription

/-! Exact full-vector phase decoding. The eight comparisons are independent;
no one-hot or reachability assumption is built into the circuit. The expanded
typed hierarchy and its verification remain under `Internal/`. -/

namespace PhaseDecode.Description

noncomputable def construction : Builder Unit := do
  let state ← input "cpu_state" (.vector 8 .bit)
  output "trap" (← Silean.Modules.EqualsConstant.place
    state (stateBits cpuStateTrap))
  output "fetch" (← Silean.Modules.EqualsConstant.place
    state (stateBits cpuStateFetch))
  output "loadRs1" (← Silean.Modules.EqualsConstant.place
    state (stateBits cpuStateLdRs1))
  output "loadRs2" (← Silean.Modules.EqualsConstant.place
    state (stateBits cpuStateLdRs2))
  output "execute" (← Silean.Modules.EqualsConstant.place
    state (stateBits cpuStateExec))
  output "shift" (← Silean.Modules.EqualsConstant.place
    state (stateBits cpuStateShift))
  output "store" (← Silean.Modules.EqualsConstant.place
    state (stateBits cpuStateStmem))
  output "load" (← Silean.Modules.EqualsConstant.place
    state (stateBits cpuStateLdmem))

noncomputable def description : Description := build construction

end PhaseDecode.Description

namespace PhaseDecode

/-- Phase predicates produced by a placed decoder. -/
structure PlacedOutputs where
  trap : Net .bit
  fetch : Net .bit
  loadRs1 : Net .bit
  loadRs2 : Net .bit
  execute : Net .bit
  shift : Net .bit
  store : Net .bit
  load : Net .bit

/-- Place a phase decoder under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Silean.Naming.SourceName)
    (state : Net (.vector 8 .bit)) : Builder PlacedOutputs := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .cpu_state => state
  pure {
    trap := child .trap
    fetch := child .fetch
    loadRs1 := child .loadRs1
    loadRs2 := child .loadRs2
    execute := child .execute
    shift := child .shift
    store := child .store
    load := child .load }

/-- Place a phase decoder using the next conventional indexed name. -/
noncomputable def place (state : Net (.vector 8 .bit)) :
    Builder PlacedOutputs := do
  let child ← placeIndexed "control_phase_decode" design fun
    | .cpu_state => state
  pure {
    trap := child .trap
    fetch := child .fetch
    loadRs1 := child .loadRs1
    loadRs2 := child .loadRs2
    execute := child .execute
    shift := child .shift
    store := child .store
    load := child .load }

attribute [circuit_description] placeNamed place

end PhaseDecode

end PicoRV.Control
