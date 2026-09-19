import PicoRV.Control.Internal.ControlCommandFinishStructure
import PicoRV.Authoring.CircuitLogic
import Silean.Authoring.ModuleCycleContract

namespace PicoRV.Control.CommandFinish

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring.CircuitLogic
open scoped Silean.Authoring.CircuitLogic

/-! # Command finishing

The final command-priority layer receives a complete proposed transition. When
`clear` is high it first clears all four memory commands, then reasserts the
three commands represented by the blocking `set_mem_do_*` intents. Every
other state field passes through unchanged.

The concise definition below makes that priority visible. The expanded typed
hierarchy and its certification remain under `Internal/`. -/

namespace Description

noncomputable def construction : Builder Unit := do
  let clear ← input "clear" .bit
  let transition ← input "transition" transitionType
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
  output "state" result

noncomputable def description : Description := build construction

end Description

/-! ## Placement -/

noncomputable def placeNamed (name : Naming.SourceName)
    (clear : Net .bit) (transition : Net transitionType) :
    Builder (Net stateType) := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .clear => clear
    | .transition => transition
  pure (child .state)

noncomputable def place (clear : Net .bit) (transition : Net transitionType) :
    Builder (Net stateType) := do
  let child ← placeIndexed "command_finish" design fun
    | .clear => clear
    | .transition => transition
  pure (child .state)

attribute [circuit_description] placeNamed place

/-! ## Exact cycle behavior -/

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

end PicoRV.Control.CommandFinish
