import PicoRV.Control.ControlPhaseTransition
import PicoRV.Authoring.CircuitLogic

namespace PicoRV.Control

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring
open scoped Silean.Authoring

namespace ExecuteTransition

abbrev cycleContract := PhaseTransition.cycleContract
  (fun inputs _ updated => executeTransition inputs updated)

theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs .transition =
      ((fun inputs _ updated => executeTransition inputs updated)
        (Inputs.unpack (step.inputs .inputs))
        (stateMap.unpack (step.inputs .current))
        (stateMap.unpack (step.inputs .updated))).pack :=
  (PhaseTransition.outputRule_holds_iff
    (fun inputs _ updated => executeTransition inputs updated)
    step.inputs step.currentState step.outputs).mp (allowed.1 .apply)

/-! # Execute transition

Execute has two complete transition candidates. The branch candidate keeps the
source's independent priorities visible: `mem_done` may return to fetch, while
a taken branch independently suppresses `decoder_trigger` and raises
`setRinst`. The final mux selects the branch candidate by instruction class.
The expanded typed hierarchy and verification remain under `Internal/`. -/

open PhaseTransition.ports

noncomputable def construction : ModuleBuilder PhaseTransition.ports Unit := do
  let inputs ← input .inputs
  discard (input .current)
  let updated ← input .updated
  let inputsFields ← split ControlInputs.layout inputs
  let updatedFields ← split ControlState.layout updated
  let falseBit ← constant .bit false
  let trueBit ← constant .bit true
  let zeroRd ← constant (.vector 5 .bit) (fiveBitsOfNat 0)
  let fetchState ← constant (.vector 8 .bit) (stateBits cpuStateFetch)

  let branchPhase ← mux (inputsFields .mem_done)
    (updatedFields .cpu_state) fetchState
  let branchDecoder ← mux (inputsFields .alu_out_0)
    (updatedFields .decoder_trigger) falseBit
  let branchState ← update stateMap ControlState.schema
    updatedFields fun
      | .cpu_state => some branchPhase
      | .latched_store | .latched_branch => some (inputsFields .alu_out_0)
      | .latched_rd => some zeroRd
      | .decoder_trigger => some branchDecoder
      | _ => none
  let branchTransition ← combine
    TransitionValue.signalMap TransitionValue.schema fun
      | .state => branchState
      | .setRinst => inputsFields .alu_out_0
      | .setRdata | .setWdata => falseBit

  let ordinaryState ← update stateMap ControlState.schema
    updatedFields fun
      | .cpu_state => some fetchState
      | .latched_store | .latched_stalu => some trueBit
      | .latched_branch => some (inputsFields .instr_jalr)
      | _ => none
  let ordinaryTransition ← combine
    TransitionValue.signalMap TransitionValue.schema fun
      | .state => ordinaryState
      | .setRinst | .setRdata | .setWdata => falseBit

  output .transition (← mux
    (inputsFields .is_beq_bne_blt_bge_bltu_bgeu)
    ordinaryTransition branchTransition)

noncomputable def description : Description :=
  ModuleBuilder.build PhaseTransition.Naming.ports construction

end ExecuteTransition

end PicoRV.Control
