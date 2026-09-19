import PicoRV.Memory.Internal.MemoryLookaheadCaptureStructure
import PicoRV.Memory.MemoryLookahead
import PicoRV.Authoring.CircuitLogic

namespace PicoRV.Memory

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring.CircuitLogic
open scoped Silean.Authoring.CircuitLogic

/-! # Look-ahead capture

This stage copies an active look-ahead request into the proposed memory state
before the phase-specific update. Reads preserve a zero write mask; writes
capture their formatted data and strobe. The child module already identifies
the look-ahead stage, so it uses the ordinary indexed placement. The expanded
typed hierarchy and verification remain under `Internal/`. -/

namespace LookaheadCapture.Description

noncomputable def construction : Builder Unit := do
  let inputs ← input "inputs" inputsType
  let current ← input "current" stateType
  let updated ← input "updated" stateType
  let inputsFields ← split MemoryInputs.layout inputs
  let updatedFields ← split MemoryState.layout updated

  let lookahead ← Lookahead.place
    (inputsFields .resetn) (inputsFields .mem_do_prefetch)
    (inputsFields .mem_do_rinst) (inputsFields .mem_do_rdata)
    (inputsFields .mem_do_wdata) (inputsFields .next_pc)
    (inputsFields .reg_op1) (inputsFields .reg_op2)
    (inputsFields .mem_wordsize) current
  let active ← lookahead.memLaRead ||| lookahead.memLaWrite
  let zeroMask ← constant (.vector 4 .bit) (maskOfNat 0)
  let writeMask ← mux lookahead.memLaWrite zeroMask lookahead.memLaWstrb
  let address ← mux active (updatedFields .mem_addr) lookahead.memLaAddr
  let mask ← mux active (updatedFields .mem_wstrb) writeMask
  let writeData ← mux lookahead.memLaWrite
    (updatedFields .mem_wdata) lookahead.memLaWdata
  let result ← update stateMap MemoryState.schema updatedFields fun
    | .mem_addr => some address
    | .mem_wdata => some writeData
    | .mem_wstrb => some mask
    | _ => none
  output "state" result

noncomputable def description : Description := build construction

end LookaheadCapture.Description

namespace LookaheadCapture

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
  let child ← placeIndexed "lookahead_capture" design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure (child .state)

attribute [circuit_description] placeNamed place

end LookaheadCapture

end PicoRV.Memory
