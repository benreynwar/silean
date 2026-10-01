import PicoRV.Control.ControlAlignmentDerived
import PicoRV.ControlContract
import PicoRV.Authoring.CircuitLogic
import Silean.Authoring.ModuleCycleContract

namespace PicoRV.Control

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring
open scoped Silean.Authoring

namespace ResetAndAlignmentOverride

module_ports ports where
  input inputs (schema := ControlInputs.schema) : inputsType,
  input current (schema := ControlState.schema) : stateType,
  input baseline (schema := ControlState.schema) : stateType,
  input selected (schema := TransitionValue.schema) : transitionType,
  output transition (schema := TransitionValue.schema) : transitionType

def outputTransition (inputs : inputMap.Values) : Transition :=
  resetAndAlignmentTransition (Inputs.unpack (inputs .inputs))
    (stateMap.unpack (inputs .current))
    (stateMap.unpack (inputs .baseline))
    (Transition.unpack (inputs .selected))

def outputRule : Silean.Contracts.Cycle.CycleOutputRule ports emptySignalMap where
  readsInputs := .all inputMap
  writesOutputs := .all outputMap
  target inputs _ := fun | .transition => (outputTransition inputs).pack

module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule apply := outputRule
  state_rule := Silean.Contracts.Cycle.CycleStateRule.empty _

@[simp] theorem outputRule_holds_iff (inputs : inputMap.Values)
    (state : emptySignalMap.Values) (outputs : outputMap.Values) :
    outputRule.Holds inputs state outputs ↔
      outputs .transition = (outputTransition inputs).pack := by
  simp only [Silean.Contracts.Cycle.CycleOutputRule.Holds, outputRule,
    Silean.SignalGroup.all_matches]
  constructor
  · intro equal; exact congrFun equal .transition
  · intro equal; funext output; cases output; exact equal

theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs .transition = (outputTransition step.inputs).pack :=
  (outputRule_holds_iff step.inputs step.currentState step.outputs).mp
    (allowed.1 .apply)

/-! # Reset and alignment override

This module makes the final two priority layers before command completion
visible. Reset first replaces the selected phase transition with one derived
from the baseline. When reset is inactive, address misalignment overrides only
the selected transition's phase with `trap`; its command intents and all other
proposed fields survive. Alignment is deliberately checked from the original
state. The expanded typed hierarchy and verification remain under `Internal/`.
-/

open ports

noncomputable def construction : ModuleBuilder ports Unit := do
  let inputs ← input .inputs
  let current ← input .current
  let baseline ← input .baseline
  let selected ← input .selected
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
  output .transition (← mux alignmentEnabled
    resetSelection alignmentTransition)

noncomputable def description : Description :=
  ModuleBuilder.build Naming.ports construction

end ResetAndAlignmentOverride

end PicoRV.Control
