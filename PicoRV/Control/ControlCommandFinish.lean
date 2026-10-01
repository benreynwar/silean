import PicoRV.ControlContract
import PicoRV.Authoring.CircuitLogic
import Silean.Authoring.ModuleCycleContract

namespace PicoRV.Control.CommandFinish

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring
open scoped Silean.Authoring

/-! # Command finishing

The final command-priority layer receives a complete proposed transition. When
`clear` is high it first clears all four memory commands, then reasserts the
three commands represented by the blocking `set_mem_do_*` intents. Every
other state field passes through unchanged.

The concise definition below makes that priority visible. The expanded typed
hierarchy and its certification remain under `Internal/`. -/

module_ports ports where
  input clear : .bit,
  input transition (schema := TransitionValue.schema) : transitionType,
  output state (schema := ControlState.schema) : stateType

def outputState (inputs : inputMap.Values) : stateMap.Values :=
  finishCommands (inputs .clear) (Transition.unpack (inputs .transition))

def outputValues (inputs : inputMap.Values) : outputMap.Values
  | .state => stateMap.pack (outputState inputs)

def outputRule : Silean.Contracts.Cycle.CycleOutputRule ports emptySignalMap where
  readsInputs := .all inputMap
  writesOutputs := .all outputMap
  target inputs _ := outputValues inputs

module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule apply := outputRule
  state_rule := Silean.Contracts.Cycle.CycleStateRule.empty _

@[simp] theorem outputRule_holds_iff
    (inputs : inputMap.Values) (state : emptySignalMap.Values)
    (outputs : outputMap.Values) :
    outputRule.Holds inputs state outputs ↔
      outputs .state = stateMap.pack (outputState inputs) := by
  simp only [Silean.Contracts.Cycle.CycleOutputRule.Holds, outputRule,
    Silean.SignalGroup.all_matches]
  constructor
  · intro equal
    exact congrFun equal .state
  · intro equal
    funext output
    cases output
    exact equal

theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs .state = stateMap.pack (outputState step.inputs) :=
  (outputRule_holds_iff step.inputs step.currentState step.outputs).mp
    (allowed.1 .apply)

open ports

noncomputable def construction : ModuleBuilder ports Unit := do
  let clear ← input .clear
  let transition ← input .transition
  let transitionFields ← split TransitionValue.layout transition
  let stateFields ← split ControlState.layout (transitionFields .state)
  let notClear ← !! clear
  let keepPrefetch ← stateFields .mem_do_prefetch &&& notClear
  let finishRinst ←
    (← stateFields .mem_do_rinst &&& notClear) ||| transitionFields .setRinst
  let finishRdata ←
    (← stateFields .mem_do_rdata &&& notClear) ||| transitionFields .setRdata
  let finishWdata ←
    (← stateFields .mem_do_wdata &&& notClear) ||| transitionFields .setWdata
  let result ← update stateMap ControlState.schema stateFields fun
    | .mem_do_prefetch => some keepPrefetch
    | .mem_do_rinst => some finishRinst
    | .mem_do_rdata => some finishRdata
    | .mem_do_wdata => some finishWdata
    | _ => none
  output .state result

noncomputable def description : Description :=
  ModuleBuilder.build Naming.ports construction

end PicoRV.Control.CommandFinish
