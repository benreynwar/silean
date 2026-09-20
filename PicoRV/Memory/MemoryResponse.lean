import PicoRV.Memory.Internal.MemoryResponseStructure
import PicoRV.Authoring.CircuitLogic
import Silean.Modules.EqualsConstant.EqualsConstant

namespace PicoRV.Memory

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring
open scoped Silean.Authoring

/-! # Memory response

A normal completion requires an accepted non-idle request and a live
read/write command. A prefetched instruction can instead complete later from
phase 3 without another transfer. Response data bypasses the saved value only
on an accepted transfer. The expanded typed hierarchy and verification remain
under `Internal/`. -/

namespace Response.Description

noncomputable def construction : Builder Unit := do
  let resetn ← input "resetn" .bit
  let memDoRinst ← input "mem_do_rinst" .bit
  let memDoRdata ← input "mem_do_rdata" .bit
  let memDoWdata ← input "mem_do_wdata" .bit
  let memReady ← input "mem_ready" .bit
  let memRdata ← input "mem_rdata" (.vector 32 .bit)
  let current ← input "current" stateType
  let currentFields ← split MemoryState.layout current

  let transfer ← currentFields .mem_valid &&& memReady
  let idle ← Silean.Modules.EqualsConstant.place
    (currentFields .mem_state) (stateOfNat 0)
  let transferNonIdle ← transfer &&& (← !! idle)
  let activeCommand ←
    (← memDoRinst ||| memDoRdata) ||| memDoWdata
  let ordinaryCompletion ← transferNonIdle &&& activeCommand
  let prefetched ← Silean.Modules.EqualsConstant.place
    (currentFields .mem_state) (stateOfNat 3)
  let delayedCompletion ← prefetched &&& memDoRinst
  let completion ← ordinaryCompletion ||| delayedCompletion

  output "mem_done" (← resetn &&& completion)
  output "mem_rdata_latched" (← mux transfer
    (currentFields .mem_rdata_q) memRdata)

noncomputable def description : Description := build construction

end Response.Description

namespace Response

structure PlacedOutputs where
  memDone : Net .bit
  memRdataLatched : Net (.vector 32 .bit)

noncomputable def placeNamed (name : Naming.SourceName)
    (resetn memDoRinst memDoRdata memDoWdata memReady : Net .bit)
    (memRdata : Net (.vector 32 .bit)) (current : Net stateType) :
    Builder PlacedOutputs := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .resetn => resetn
    | .mem_do_rinst => memDoRinst
    | .mem_do_rdata => memDoRdata
    | .mem_do_wdata => memDoWdata
    | .mem_ready => memReady
    | .mem_rdata => memRdata
    | .current => current
  pure ⟨child .mem_done, child .mem_rdata_latched⟩

noncomputable def place
    (resetn memDoRinst memDoRdata memDoWdata memReady : Net .bit)
    (memRdata : Net (.vector 32 .bit)) (current : Net stateType) :
    Builder PlacedOutputs := do
  let child ← placeIndexed "memory_response" design fun
    | .resetn => resetn
    | .mem_do_rinst => memDoRinst
    | .mem_do_rdata => memDoRdata
    | .mem_do_wdata => memDoWdata
    | .mem_ready => memReady
    | .mem_rdata => memRdata
    | .current => current
  pure ⟨child .mem_done, child .mem_rdata_latched⟩

attribute [circuit_description] placeNamed place

end Response

end PicoRV.Memory
