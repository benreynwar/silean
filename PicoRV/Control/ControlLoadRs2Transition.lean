import PicoRV.Control.ControlPhaseTransition
import PicoRV.Authoring.CircuitLogic

namespace PicoRV.Control

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring
open scoped Silean.Authoring

namespace LoadRs2Transition

abbrev cycleContract := PhaseTransition.cycleContract
  (fun inputs _ updated => loadRs2Transition inputs updated)

theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs .transition =
      ((fun inputs _ updated => loadRs2Transition inputs updated)
        (Inputs.unpack (step.inputs .inputs))
        (stateMap.unpack (step.inputs .current))
        (stateMap.unpack (step.inputs .updated))).pack :=
  (PhaseTransition.outputRule_holds_iff
    (fun inputs _ updated => loadRs2Transition inputs updated)
    step.inputs step.currentState step.outputs).mp (allowed.1 .apply)

/-! # Load-RS2 transition

Load-RS2 preserves the source's ordered three-way decision: stores have
priority over register shifts, and every other instruction enters execute.
Parallel mux chains select the next phase and instruction-read command without
assuming that the selectors are mutually exclusive. The expanded typed
hierarchy and verification remain under `Internal/`. -/

open PhaseTransition.ports

noncomputable def construction : ModuleBuilder PhaseTransition.ports Unit := do
  let inputs ← input .inputs
  discard (input .current)
  let updated ← input .updated
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
  output .transition result

noncomputable def description : Description :=
  ModuleBuilder.build PhaseTransition.Naming.ports construction

end LoadRs2Transition

end PicoRV.Control
