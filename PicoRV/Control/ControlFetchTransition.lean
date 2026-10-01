import PicoRV.Control.ControlPhaseTransition
import PicoRV.Authoring.CircuitLogic

namespace PicoRV.Control

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring
open scoped Silean.Authoring

namespace FetchTransition

abbrev cycleContract := PhaseTransition.cycleContract fetchTransition

theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs .transition =
      (fetchTransition (Inputs.unpack (step.inputs .inputs))
        (stateMap.unpack (step.inputs .current))
        (stateMap.unpack (step.inputs .updated))).pack :=
  (PhaseTransition.outputRule_holds_iff fetchTransition
    step.inputs step.currentState step.outputs).mp (allowed.1 .apply)

/-! # Fetch transition

Fetch deliberately reads the pre-edge `decoder_trigger`. The common state
captures the destination register and clears transient metadata. An absent
decode requests an instruction and stays in fetch. A present decode selects
JAL (reissue instruction read and mark a branch) or the ordinary/JALR path
(enter load-RS1 and enable prefetch except for JALR). The expanded typed
hierarchy and verification remain under `Internal/`. -/

open PhaseTransition.ports

noncomputable def construction : ModuleBuilder PhaseTransition.ports Unit := do
  let inputs ← input .inputs
  let current ← input .current
  let updated ← input .updated
  let inputsFields ← split ControlInputs.layout inputs
  let currentFields ← split ControlState.layout current
  let updatedFields ← split ControlState.layout updated
  let falseBit ← constant .bit false
  let trueBit ← constant .bit true
  let wordSize ← constant (.vector 2 .bit) (twoBitsOfNat 0)
  let loadRs1State ← constant (.vector 8 .bit) (stateBits cpuStateLdRs1)
  let notDecoder ← !! (currentFields .decoder_trigger)
  let notJalr ← !! (inputsFields .instr_jalr)

  let commonState ← update stateMap ControlState.schema
    updatedFields fun
      | .latched_store | .latched_stalu | .latched_branch
      | .latched_is_lu | .latched_is_lh | .latched_is_lb => some falseBit
      | .latched_rd => some (inputsFields .decoded_rd)
      | .mem_wordsize => some wordSize
      | .mem_do_rinst => some notDecoder
      | _ => none
  let commonFields ← split ControlState.layout commonState
  let jalState ← update stateMap ControlState.schema
    commonFields fun
      | .latched_branch | .mem_do_rinst => some trueBit
      | _ => none
  let ordinaryState ← update stateMap ControlState.schema
    commonFields fun
      | .cpu_state => some loadRs1State
      | .mem_do_prefetch => some notJalr
      | .mem_do_rinst => some falseBit
      | _ => none
  let decodedState ← mux (inputsFields .instr_jal) ordinaryState jalState
  let finalState ← mux notDecoder decodedState commonState
  let result ← combine TransitionValue.signalMap
    TransitionValue.schema fun
      | .state => finalState
      | .setRinst | .setRdata | .setWdata => falseBit
  output .transition result

noncomputable def description : Description :=
  ModuleBuilder.build PhaseTransition.Naming.ports construction

end FetchTransition

end PicoRV.Control
