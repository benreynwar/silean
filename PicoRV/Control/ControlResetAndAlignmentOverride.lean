import PicoRV.Control.Internal.ControlResetAndAlignmentOverrideStructure
import PicoRV.Authoring.CircuitLogic

namespace PicoRV.Control

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring.CircuitLogic
open scoped Silean.Authoring.CircuitLogic

/-! # Reset and alignment override

This module makes the final two priority layers before command completion
visible. Reset first replaces the selected phase transition with one derived
from the baseline. When reset is inactive, address misalignment overrides only
the selected transition's phase with `trap`; its command intents and all other
proposed fields survive. Alignment is deliberately checked from the original
state. The expanded typed hierarchy and verification remain under `Internal/`.
-/

namespace ResetAndAlignmentOverride.Description

noncomputable def construction : Builder Unit := do
  let inputs ← input "inputs" inputsType
  let current ← input "current" stateType
  let baseline ← input "baseline" stateType
  let selected ← input "selected" transitionType
  let inputsFields ← split ControlInputs.layout inputs
  let baselineFields ← split ControlState.layout baseline
  let falseBit ← constant .bit false
  let fetchState ← constant (.vector 8 .bit) (stateBits cpuStateFetch)
  let trapState ← constant (.vector 8 .bit) (stateBits cpuStateTrap)

  let resetState ← update stateMap ControlState.schema
    baselineFields fun
      | .cpu_state => some fetchState
      | .latched_store | .latched_stalu | .latched_branch
      | .latched_is_lu | .latched_is_lh | .latched_is_lb => some falseBit
      | _ => none
  let resetTransition ← combine
    TransitionValue.signalMap TransitionValue.schema fun
      | .state => resetState
      | .setRinst | .setRdata | .setWdata => falseBit
  let notResetn ← !! (inputsFields .resetn)
  let resetSelection ← mux notResetn selected resetTransition

  let alignment ← Alignment.place inputs current
  let anyMisalignment ← alignment.data ||| alignment.instruction
  let alignmentEnabled ← inputsFields .resetn &&& anyMisalignment
  let selectedTransitionFields ← split TransitionValue.layout resetSelection
  let selectedStateFields ← split ControlState.layout
    (selectedTransitionFields .state)
  let alignmentState ← update stateMap ControlState.schema
    selectedStateFields fun
      | .cpu_state => some trapState
      | _ => none
  let alignmentTransition ← combine
    TransitionValue.signalMap TransitionValue.schema fun
      | .state => alignmentState
      | .setRinst => selectedTransitionFields .setRinst
      | .setRdata => selectedTransitionFields .setRdata
      | .setWdata => selectedTransitionFields .setWdata
  output "transition" (← mux alignmentEnabled
    resetSelection alignmentTransition)

noncomputable def description : Description := build construction

end ResetAndAlignmentOverride.Description

namespace ResetAndAlignmentOverride

structure PlacedOutputs where
  transition : Net transitionType

noncomputable def placeNamed (name : Naming.SourceName)
    (inputs : Net inputsType) (current baseline : Net stateType)
    (selected : Net transitionType) : Builder PlacedOutputs := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .inputs => inputs
    | .current => current
    | .baseline => baseline
    | .selected => selected
  pure ⟨child .transition⟩

noncomputable def place (inputs : Net inputsType)
    (current baseline : Net stateType) (selected : Net transitionType) :
    Builder PlacedOutputs := do
  let child ← placeIndexed "reset_alignment_override" design fun
    | .inputs => inputs
    | .current => current
    | .baseline => baseline
    | .selected => selected
  pure ⟨child .transition⟩

attribute [circuit_description] placeNamed place

end ResetAndAlignmentOverride

end PicoRV.Control
