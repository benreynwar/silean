import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts

namespace SileanTests.ModuleCycleContractAuthoring

open Silean Silean.Authoring

namespace Stateless

module_ports ports where
  input left : .bit,
  input right : .bit,
  output result : .bit

module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule result where
    reads := [left, right]
    writes := { result := left && right }
  state_rule where
    reads := []
    next := {}

example (inputs : ports.inputs.Values) (state : emptySignalMap.Values)
    (outputs : ports.outputs.Values) :
    resultRule.Holds inputs state outputs ↔
      outputs .result = (inputs .left && inputs .right) :=
  resultRule_holds_iff inputs state outputs

end Stateless

namespace MultipleOutputs

module_ports ports where
  input left : .bit,
  input right : .bit,
  output first : .bit,
  output second : .bit

module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule both where
    reads := [left, right]
    writes := {
      first := left,
      second := right }
  state_rule where
    reads := []
    next := {}

example (inputs : ports.inputs.Values) (state : emptySignalMap.Values)
    (outputs : ports.outputs.Values) :
    bothRule.Holds inputs state outputs ↔
      outputs .first = inputs .left ∧ outputs .second = inputs .right :=
  bothRule_holds_iff inputs state outputs

end MultipleOutputs

namespace Stateful

inductive State | stored
deriving Enumeration

@[reducible] def stateMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of State fun | .stored => signalType

module_ports ports (signalType : SignalType) where
  input value : signalType,
  input enable : .bit,
  output value : signalType

module_cycle_contract cycleContract (signalType : SignalType)
    for ports signalType where
  state := stateMap signalType
  output_rule observe where
    reads := []
    writes := { value := state .stored }
  state_rule where
    reads := [enable, value]
    next := { stored := bif enable then value else state .stored }

example (signalType : SignalType) (inputs : (ports signalType).inputs.Values)
    (state : (stateMap signalType).Values)
    (outputs : (ports signalType).outputs.Values) :
    (observeRule signalType).Holds inputs state outputs ↔
      outputs .value = state .stored :=
  observeRule_holds_iff signalType inputs state outputs

example (signalType : SignalType) (inputs : (ports signalType).inputs.Values)
    (state : (stateMap signalType).Values) :
    (stateRule signalType).apply inputs state .stored =
      bif inputs .enable then inputs .value else state .stored := by
  rfl

example (signalType : SignalType) :
    (observeRule signalType).readsInputs.labels = [] := rfl

example (signalType : SignalType) :
    (observeRule signalType).writesOutputs.labels = [.value] := rfl

example (signalType : SignalType) :
    (stateRule signalType).readsInputs.labels = [.enable, .value] := rfl

end Stateful

namespace ExistingStateRule

inductive State | stored
deriving Enumeration

@[reducible] def stateMap : SignalMap :=
  EnumeratedMap.of State fun | .stored => .bit

module_ports ports where
  input value : .bit,
  output value : .bit

def existingStateRule : Contracts.Cycle.CycleStateRule ports stateMap where
  readsInputs := .all inputMap
  target inputs _ := fun | .stored => inputs .value

module_cycle_contract cycleContract for ports where
  state := stateMap
  output_rule observe where
    reads := []
    writes := { value := state .stored }
  state_rule := existingStateRule

example : cycleContract.stateRule = existingStateRule := rfl

end ExistingStateRule

end SileanTests.ModuleCycleContractAuthoring
