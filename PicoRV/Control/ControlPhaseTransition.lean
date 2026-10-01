import Silean.Authoring.ModuleCycleContract
import PicoRV.ControlContract

namespace PicoRV.Control.PhaseTransition

open Silean
open Silean.Authoring
open PicoRV.Control

/-! Shared boundary and contract for the eight control-phase transitions.
Each concrete child supplies only its source-level transition function. -/

module_ports ports where
  input inputs (schema := ControlInputs.schema) : inputsType,
  input current (schema := ControlState.schema) : stateType,
  input updated (schema := ControlState.schema) : stateType,
  output transition (schema := TransitionValue.schema) : transitionType

def outputValues
    (transition : Inputs → stateMap.Values → stateMap.Values → Transition)
    (inputs : inputMap.Values) : outputMap.Values
  | .transition => (transition (Inputs.unpack (inputs .inputs))
      (stateMap.unpack (inputs .current))
      (stateMap.unpack (inputs .updated))).pack

def outputRule
    (transition : Inputs → stateMap.Values → stateMap.Values → Transition) :
    Silean.Contracts.Cycle.CycleOutputRule ports emptySignalMap where
  readsInputs := .all inputMap
  writesOutputs := .all outputMap
  target inputs _ := outputValues transition inputs

module_cycle_contract cycleContract
    (transition : Inputs → stateMap.Values → stateMap.Values → Transition)
    for ports where
  state := emptySignalMap
  output_rule apply := outputRule transition
  state_rule := Silean.Contracts.Cycle.CycleStateRule.empty _

@[simp] theorem outputRule_holds_iff
    (transition : Inputs → stateMap.Values → stateMap.Values → Transition)
    (inputs : inputMap.Values) (state : emptySignalMap.Values)
    (outputs : outputMap.Values) :
    (outputRule transition).Holds inputs state outputs ↔
      outputs .transition = (transition (Inputs.unpack (inputs .inputs))
        (stateMap.unpack (inputs .current))
        (stateMap.unpack (inputs .updated))).pack := by
  simp only [Silean.Contracts.Cycle.CycleOutputRule.Holds, outputRule,
    Silean.SignalGroup.all_matches]
  constructor
  · intro equal
    exact congrFun equal .transition
  · intro equal
    funext output
    cases output
    exact equal

end PicoRV.Control.PhaseTransition
