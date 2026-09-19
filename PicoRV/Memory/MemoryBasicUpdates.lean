import PicoRV.Authoring.CircuitLogic
import PicoRV.Memory.Internal.MemoryBasicUpdatesStructure
import Silean.Modules.EqualsConstant.EqualsConstant

/-! # Memory state-update stages

These small combinational modules are the source-ordered layers used by the
complete memory transition. Each description exposes the relevant state fields,
computes one local decision, and updates only the fields owned by that layer.
The expanded typed structures and their verification live under `Internal/`.
-/

namespace PicoRV.Memory

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring.CircuitLogic
open scoped Silean.Authoring.CircuitLogic

namespace ResponseCapture.Description

noncomputable def construction : Builder Unit := do
  let inputs ← input "inputs" inputsType
  let current ← input "current" stateType
  let inputsFields ← split MemoryInputs.layout inputs
  let currentFields ← split MemoryState.layout current
  let transfer ← currentFields .mem_valid &&& inputsFields .mem_ready
  let response ← mux transfer
    (currentFields .mem_rdata_q) (inputsFields .mem_rdata)
  output "state" (← update stateMap MemoryState.schema currentFields fun
    | .mem_rdata_q => some response
    | _ => none)

noncomputable def description : Description := build construction

end ResponseCapture.Description

namespace ResponseCapture

noncomputable def placeNamed (name : Naming.SourceName)
    (inputs : Net inputsType) (current : Net stateType) :
    Builder (Net stateType) := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .inputs => inputs
    | .current => current
  pure (child .state)

noncomputable def place (inputs : Net inputsType) (current : Net stateType) :
    Builder (Net stateType) := do
  let child ← placeIndexed "memory_response_capture" design fun
    | .inputs => inputs
    | .current => current
  pure (child .state)

attribute [circuit_description] placeNamed place

end ResponseCapture

namespace PhaseDecode.Description

noncomputable def construction : Builder Unit := do
  let state ← input "mem_state" (.vector 2 .bit)
  let idle ← Silean.Modules.EqualsConstant.place state (stateOfNat 0)
  let read ← Silean.Modules.EqualsConstant.place state (stateOfNat 1)
  let write ← Silean.Modules.EqualsConstant.place state (stateOfNat 2)
  let prefetched ← Silean.Modules.EqualsConstant.place state (stateOfNat 3)
  output "idle" idle
  output "read" read
  output "write" write
  output "prefetched" prefetched

noncomputable def description : Description := build construction

end PhaseDecode.Description

namespace PhaseDecode

structure PlacedOutputs where
  idle : Net .bit
  read : Net .bit
  write : Net .bit
  prefetched : Net .bit

noncomputable def placeNamed (name : Naming.SourceName)
    (state : Net (.vector 2 .bit)) : Builder PlacedOutputs := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .mem_state => state
  pure ⟨child .idle, child .read, child .write, child .prefetched⟩

noncomputable def place (state : Net (.vector 2 .bit)) :
    Builder PlacedOutputs := do
  let child ← placeIndexed "memory_phase_decode" design fun
    | .mem_state => state
  pure ⟨child .idle, child .read, child .write, child .prefetched⟩

attribute [circuit_description] placeNamed place

end PhaseDecode

namespace IdleUpdate.Description

noncomputable def construction : Builder Unit := do
  let inputs ← input "inputs" inputsType
  let _current ← input "current" stateType
  let updated ← input "updated" stateType
  let inputsFields ← split MemoryInputs.layout inputs
  let updatedFields ← split MemoryState.layout updated
  let instructionCommand ←
    inputsFields .mem_do_prefetch ||| inputsFields .mem_do_rinst
  let readCommand ← instructionCommand ||| inputsFields .mem_do_rdata
  let trueBit ← constant .bit true
  let falseBit ← constant .bit false
  let zeroMask ← constant (.vector 4 .bit) (maskOfNat 0)
  let readState ← constant (.vector 2 .bit) (stateOfNat 1)
  let writeState ← constant (.vector 2 .bit) (stateOfNat 2)
  let readValid ← mux readCommand (updatedFields .mem_valid) trueBit
  let readInstr ← mux readCommand (updatedFields .mem_instr) instructionCommand
  let readMask ← mux readCommand (updatedFields .mem_wstrb) zeroMask
  let readPhase ← mux readCommand (updatedFields .mem_state) readState
  let finalValid ← mux (inputsFields .mem_do_wdata) readValid trueBit
  let finalInstr ← mux (inputsFields .mem_do_wdata) readInstr falseBit
  let finalPhase ← mux (inputsFields .mem_do_wdata) readPhase writeState
  output "state" (← update stateMap MemoryState.schema updatedFields fun
    | .mem_state => some finalPhase
    | .mem_valid => some finalValid
    | .mem_instr => some finalInstr
    | .mem_wstrb => some readMask
    | _ => none)

noncomputable def description : Description := build construction

end IdleUpdate.Description

namespace IdleUpdate

noncomputable def placeNamed (name : Naming.SourceName)
    (inputs : Net inputsType) (current updated : Net stateType) :
    Builder (Net stateType) := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure (child .state)

noncomputable def place (inputs : Net inputsType)
    (current updated : Net stateType) : Builder (Net stateType) := do
  let child ← placeIndexed "memory_idle_update" design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure (child .state)

attribute [circuit_description] placeNamed place

end IdleUpdate

namespace ReadUpdate.Description

noncomputable def construction : Builder Unit := do
  let inputs ← input "inputs" inputsType
  let current ← input "current" stateType
  let updated ← input "updated" stateType
  let inputsFields ← split MemoryInputs.layout inputs
  let currentFields ← split MemoryState.layout current
  let updatedFields ← split MemoryState.layout updated
  let transfer ← currentFields .mem_valid &&& inputsFields .mem_ready
  let activeRead ← inputsFields .mem_do_rinst ||| inputsFields .mem_do_rdata
  let falseBit ← constant .bit false
  let idleState ← constant (.vector 2 .bit) (stateOfNat 0)
  let prefetchedState ← constant (.vector 2 .bit) (stateOfNat 3)
  let completedPhase ← mux activeRead prefetchedState idleState
  let valid ← mux transfer (updatedFields .mem_valid) falseBit
  let phase ← mux transfer (updatedFields .mem_state) completedPhase
  output "state" (← update stateMap MemoryState.schema updatedFields fun
    | .mem_state => some phase
    | .mem_valid => some valid
    | _ => none)

noncomputable def description : Description := build construction

end ReadUpdate.Description

namespace ReadUpdate

noncomputable def placeNamed (name : Naming.SourceName)
    (inputs : Net inputsType) (current updated : Net stateType) :
    Builder (Net stateType) := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure (child .state)

noncomputable def place (inputs : Net inputsType)
    (current updated : Net stateType) : Builder (Net stateType) := do
  let child ← placeIndexed "memory_read_update" design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure (child .state)

attribute [circuit_description] placeNamed place

end ReadUpdate

namespace WriteUpdate.Description

noncomputable def construction : Builder Unit := do
  let inputs ← input "inputs" inputsType
  let current ← input "current" stateType
  let updated ← input "updated" stateType
  let inputsFields ← split MemoryInputs.layout inputs
  let currentFields ← split MemoryState.layout current
  let updatedFields ← split MemoryState.layout updated
  let transfer ← currentFields .mem_valid &&& inputsFields .mem_ready
  let falseBit ← constant .bit false
  let idleState ← constant (.vector 2 .bit) (stateOfNat 0)
  let valid ← mux transfer (updatedFields .mem_valid) falseBit
  let phase ← mux transfer (updatedFields .mem_state) idleState
  output "state" (← update stateMap MemoryState.schema updatedFields fun
    | .mem_state => some phase
    | .mem_valid => some valid
    | _ => none)

noncomputable def description : Description := build construction

end WriteUpdate.Description

namespace WriteUpdate

noncomputable def placeNamed (name : Naming.SourceName)
    (inputs : Net inputsType) (current updated : Net stateType) :
    Builder (Net stateType) := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure (child .state)

noncomputable def place (inputs : Net inputsType)
    (current updated : Net stateType) : Builder (Net stateType) := do
  let child ← placeIndexed "memory_write_update" design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure (child .state)

attribute [circuit_description] placeNamed place

end WriteUpdate

namespace PrefetchedUpdate.Description

noncomputable def construction : Builder Unit := do
  let inputs ← input "inputs" inputsType
  let _current ← input "current" stateType
  let updated ← input "updated" stateType
  let inputsFields ← split MemoryInputs.layout inputs
  let updatedFields ← split MemoryState.layout updated
  let idleState ← constant (.vector 2 .bit) (stateOfNat 0)
  let phase ← mux (inputsFields .mem_do_rinst)
    (updatedFields .mem_state) idleState
  output "state" (← update stateMap MemoryState.schema updatedFields fun
    | .mem_state => some phase
    | _ => none)

noncomputable def description : Description := build construction

end PrefetchedUpdate.Description

namespace PrefetchedUpdate

noncomputable def placeNamed (name : Naming.SourceName)
    (inputs : Net inputsType) (current updated : Net stateType) :
    Builder (Net stateType) := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure (child .state)

noncomputable def place (inputs : Net inputsType)
    (current updated : Net stateType) : Builder (Net stateType) := do
  let child ← placeIndexed "memory_prefetched_update" design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure (child .state)

attribute [circuit_description] placeNamed place

end PrefetchedUpdate

namespace ResetTrapOverride.Description

noncomputable def construction : Builder Unit := do
  let inputs ← input "inputs" inputsType
  let captured ← input "captured" stateType
  let normal ← input "normal" stateType
  let inputsFields ← split MemoryInputs.layout inputs
  let capturedFields ← split MemoryState.layout captured
  let notResetn ← !! (inputsFields .resetn)
  let resetOrTrap ← notResetn ||| inputsFields .trap
  let clearValid ← notResetn ||| inputsFields .mem_ready
  let falseBit ← constant .bit false
  let idleState ← constant (.vector 2 .bit) (stateOfNat 0)
  let overridePhase ← mux (inputsFields .resetn)
    idleState (capturedFields .mem_state)
  let overrideValid ← mux clearValid (capturedFields .mem_valid) falseBit
  let overrideValue ← update stateMap MemoryState.schema capturedFields fun
    | .mem_state => some overridePhase
    | .mem_valid => some overrideValid
    | _ => none
  output "state" (← mux resetOrTrap normal overrideValue)

noncomputable def description : Description := build construction

end ResetTrapOverride.Description

namespace ResetTrapOverride

noncomputable def placeNamed (name : Naming.SourceName)
    (inputs : Net inputsType) (captured normal : Net stateType) :
    Builder (Net stateType) := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .inputs => inputs
    | .captured => captured
    | .normal => normal
  pure (child .state)

noncomputable def place (inputs : Net inputsType)
    (captured normal : Net stateType) : Builder (Net stateType) := do
  let child ← placeIndexed "memory_reset_trap_override" design fun
    | .inputs => inputs
    | .captured => captured
    | .normal => normal
  pure (child .state)

attribute [circuit_description] placeNamed place

end ResetTrapOverride

end PicoRV.Memory
