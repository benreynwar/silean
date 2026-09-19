import PicoRV.Authoring.CircuitLogic
import PicoRV.Memory.Internal.MemoryNextStructure
import PicoRV.Memory.MemoryBasicUpdates
import PicoRV.Memory.MemoryLookaheadCapture

namespace PicoRV.Memory

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring.CircuitLogic

/-! # Complete memory-state update

Response capture is computed first, then look-ahead field capture, then all four
phase candidates. The old phase selects one candidate before reset and trap
override it. In particular, the final override starts from the
response-captured state so a simultaneous transfer is retained, matching the
source's separate clocked process. -/

namespace Next.Description

noncomputable def construction : Builder Unit := do
  let inputs ← input "inputs" inputsType
  let current ← input "current" stateType
  let currentFields ← split MemoryState.layout current
  let captured ← ResponseCapture.place inputs current
  let lookahead ← LookaheadCapture.place inputs current captured
  let phase ← PhaseDecode.place (currentFields .mem_state)
  let idle ← IdleUpdate.place inputs current lookahead
  let read ← ReadUpdate.place inputs current lookahead
  let write ← WriteUpdate.place inputs current lookahead
  let prefetched ← PrefetchedUpdate.place inputs current lookahead
  let selected ← mux phase.write prefetched write
  let selected ← mux phase.read selected read
  let selected ← mux phase.idle selected idle
  output "state" (← ResetTrapOverride.place inputs captured selected)

noncomputable def description : Description := build construction

end Next.Description

namespace Next

noncomputable def placeNamed (name : Naming.SourceName)
    (inputs : Net inputsType) (current : Net stateType) :
    Builder (Net stateType) := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .inputs => inputs
    | .current => current
  pure (child .state)

noncomputable def place (inputs : Net inputsType) (current : Net stateType) :
    Builder (Net stateType) := do
  let child ← placeIndexed "memory_next" design fun
    | .inputs => inputs
    | .current => current
  pure (child .state)

attribute [circuit_description] placeNamed place

end Next

end PicoRV.Memory
