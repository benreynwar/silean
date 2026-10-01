import PicoRV.Control.ControlPhaseTransition
import PicoRV.Authoring.CircuitLogic
import Silean.Modules.EqualsConstant.EqualsConstantDerived

namespace PicoRV.Control

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring
open scoped Silean.Authoring

namespace ShiftTransition

abbrev cycleContract := PhaseTransition.cycleContract
  (fun inputs _ updated => shiftTransition inputs updated)

theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs .transition =
      ((fun inputs _ updated => shiftTransition inputs updated)
        (Inputs.unpack (step.inputs .inputs))
        (stateMap.unpack (step.inputs .current))
        (stateMap.unpack (step.inputs .updated))).pack :=
  (PhaseTransition.outputRule_holds_iff
    (fun inputs _ updated => shiftTransition inputs updated)
    step.inputs step.currentState step.outputs).mp (allowed.1 .apply)

/-! # Shift transition

Shift always marks a pending register write. Only an exactly zero five-bit
shift count returns to fetch and promotes prefetch to instruction read; a
nonzero count retains both the phase and existing read command. The expanded
typed hierarchy and verification remain under `Internal/`. -/

open PhaseTransition.ports

noncomputable def construction : ModuleBuilder PhaseTransition.ports Unit := do
  let inputs ← input .inputs
  discard (input .current)
  let updated ← input .updated
  let inputsFields ← split ControlInputs.layout inputs
  let updatedFields ← split ControlState.layout updated
  let falseBit ← constant .bit false
  let trueBit ← constant .bit true
  let fetchState ← constant (.vector 8 .bit) (stateBits cpuStateFetch)
  let shiftIsZero ← Silean.Modules.EqualsConstant.place
    (inputsFields .reg_sh) (fiveBitsOfNat 0)
  let selectedPhase ← mux shiftIsZero
    (updatedFields .cpu_state) fetchState
  let selectedRinst ← mux shiftIsZero
    (updatedFields .mem_do_rinst) (updatedFields .mem_do_prefetch)
  let resultState ← update stateMap ControlState.schema
    updatedFields fun
      | .cpu_state => some selectedPhase
      | .latched_store => some trueBit
      | .mem_do_rinst => some selectedRinst
      | _ => none
  let result ← combine TransitionValue.signalMap
    TransitionValue.schema fun
      | .state => resultState
      | .setRinst | .setRdata | .setWdata => falseBit
  output .transition result

noncomputable def description : Description :=
  ModuleBuilder.build PhaseTransition.Naming.ports construction

end ShiftTransition

end PicoRV.Control
