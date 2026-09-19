import PicoRV.Control.Internal.ControlLoadRs2TransitionStructure
import PicoRV.Authoring.CircuitLogic

namespace PicoRV.Control

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring.CircuitLogic
open scoped Silean.Authoring.CircuitLogic

/-! # Load-RS2 transition

Load-RS2 preserves the source's ordered three-way decision: stores have
priority over register shifts, and every other instruction enters execute.
Parallel mux chains select the next phase and instruction-read command without
assuming that the selectors are mutually exclusive. The expanded typed
hierarchy and verification remain under `Internal/`. -/

namespace LoadRs2Transition.Description

noncomputable def construction : Builder Unit := do
  let inputs ← input "inputs" inputsType
  discard (input "current" stateType)
  let updated ← input "updated" stateType
  let inputsFields ← split ControlInputs.layout inputs
  let updatedFields ← split ControlState.layout updated
  let falseBit ← constant .bit false
  let trueBit ← constant .bit true
  let executeState ← constant (.vector 8 .bit) (stateBits cpuStateExec)
  let shiftState ← constant (.vector 8 .bit) (stateBits cpuStateShift)
  let storeState ← constant (.vector 8 .bit) (stateBits cpuStateStmem)
  let shiftPhase ← mux
    (inputsFields .is_sll_srl_sra) executeState shiftState
  let shiftRinst ← mux
    (inputsFields .is_sll_srl_sra)
    (updatedFields .mem_do_prefetch) (updatedFields .mem_do_rinst)
  let storePhase ← mux
    (inputsFields .is_sb_sh_sw) shiftPhase storeState
  let storeRinst ← mux
    (inputsFields .is_sb_sh_sw) shiftRinst trueBit
  let resultState ← update stateMap ControlState.schema
    updatedFields fun
      | .cpu_state => some storePhase
      | .mem_do_rinst => some storeRinst
      | _ => none
  let result ← combine TransitionValue.signalMap
    TransitionValue.schema fun
      | .state => resultState
      | .setRinst | .setRdata | .setWdata => falseBit
  output "transition" result

noncomputable def description : Description := build construction

end LoadRs2Transition.Description

namespace LoadRs2Transition

structure PlacedOutputs where
  transition : Net transitionType

noncomputable def placeNamed (name : Naming.SourceName)
    (inputs : Net inputsType) (current updated : Net stateType) :
    Builder PlacedOutputs := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure ⟨child .transition⟩

noncomputable def place (inputs : Net inputsType)
    (current updated : Net stateType) : Builder PlacedOutputs := do
  let child ← placeIndexed "load_rs2_transition" design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure ⟨child .transition⟩

attribute [circuit_description] placeNamed place

end LoadRs2Transition

end PicoRV.Control
