import PicoRV.DatapathContract

namespace PicoRV.Datapath

open Silean
open Silean.Authoring

/-! Combinational contracts used to construct `PicoRVDatapathNext`. Their
boundaries carry the shared named input and state aggregates, while their
results are stated using the natural transition functions in `DatapathContract.lean`.
-/

namespace PhaseDecode

module_ports ports where
  input cpu_state : .vector 8 .bit,
  output fetch : .bit,
  output loadRs1 : .bit,
  output loadRs2 : .bit,
  output execute : .bit,
  output shift : .bit,
  output store : .bit,
  output load : .bit

def outputValues (inputs : inputMap.Values) : outputMap.Values
  | .fetch => decide (Silean.BitVector.toNat 8 (inputs .cpu_state) = cpuStateFetch)
  | .loadRs1 => decide (Silean.BitVector.toNat 8 (inputs .cpu_state) = cpuStateLdRs1)
  | .loadRs2 => decide (Silean.BitVector.toNat 8 (inputs .cpu_state) = cpuStateLdRs2)
  | .execute => decide (Silean.BitVector.toNat 8 (inputs .cpu_state) = cpuStateExec)
  | .shift => decide (Silean.BitVector.toNat 8 (inputs .cpu_state) = cpuStateShift)
  | .store => decide (Silean.BitVector.toNat 8 (inputs .cpu_state) = cpuStateStmem)
  | .load => decide (Silean.BitVector.toNat 8 (inputs .cpu_state) = cpuStateLdmem)

def outputRule : Silean.Contracts.Cycle.CycleOutputRule ports emptySignalMap where
  readsInputs := .all inputMap
  writesOutputs := .all outputMap
  target inputs _ := outputValues inputs

module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule apply := outputRule
  state_rule := Silean.Contracts.Cycle.CycleStateRule.empty _

@[simp] theorem outputRule_holds_iff (inputs : inputMap.Values)
    (state : emptySignalMap.Values) (outputs : outputMap.Values) :
    outputRule.Holds inputs state outputs ↔ outputs = outputValues inputs := by
  simp [Silean.Contracts.Cycle.CycleOutputRule.Holds, outputRule,
    Silean.SignalGroup.all_matches]

end PhaseDecode

namespace StateUpdate

module_ports ports where
  input inputs (schema := DatapathInputs.schema) : inputsType,
  input current (schema := DatapathState.schema) : stateType,
  input updated (schema := DatapathState.schema) : stateType,
  output state (schema := DatapathState.schema) : stateType

def outputState
    (transition : Inputs → stateMap.Values → stateMap.Values → stateMap.Values)
    (inputs : inputMap.Values) : stateMap.Values :=
  transition (Inputs.unpack (inputs .inputs))
    (stateMap.unpack (inputs .current))
    (stateMap.unpack (inputs .updated))

def outputRule
    (transition : Inputs → stateMap.Values → stateMap.Values → stateMap.Values) :
    Silean.Contracts.Cycle.CycleOutputRule ports emptySignalMap where
  readsInputs := .all inputMap
  writesOutputs := .all outputMap
  target inputs _ := fun | .state => stateMap.pack (outputState transition inputs)

module_cycle_contract cycleContract
    (transition : Inputs → stateMap.Values → stateMap.Values → stateMap.Values)
    for ports where
  state := emptySignalMap
  output_rule apply := outputRule transition
  state_rule := Silean.Contracts.Cycle.CycleStateRule.empty _

@[simp] theorem outputRule_holds_iff
    (transition : Inputs → stateMap.Values → stateMap.Values → stateMap.Values)
    (inputs : inputMap.Values) (state : emptySignalMap.Values)
    (outputs : outputMap.Values) :
    (outputRule transition).Holds inputs state outputs ↔
      outputs .state = stateMap.pack (outputState transition inputs) := by
  simp only [Silean.Contracts.Cycle.CycleOutputRule.Holds, outputRule,
    Silean.SignalGroup.all_matches]
  constructor
  · intro equal; exact congrFun equal .state
  · intro equal; funext output; cases output; exact equal

end StateUpdate

namespace FetchUpdate
abbrev cycleContract := StateUpdate.cycleContract fetchNextState
end FetchUpdate

namespace LoadRs1Update
abbrev cycleContract := StateUpdate.cycleContract loadRs1NextState
end LoadRs1Update

namespace LoadRs2Update
abbrev cycleContract := StateUpdate.cycleContract
  (fun inputs _ updated => loadRs2NextState inputs updated)
end LoadRs2Update

namespace ExecuteUpdate
abbrev cycleContract := StateUpdate.cycleContract executeNextState
end ExecuteUpdate

namespace ShiftUpdate
abbrev cycleContract := StateUpdate.cycleContract shiftNextState
end ShiftUpdate

namespace StoreUpdate
abbrev cycleContract := StateUpdate.cycleContract (memoryNextState false)
end StoreUpdate

namespace LoadUpdate
abbrev cycleContract := StateUpdate.cycleContract (memoryNextState true)
end LoadUpdate

namespace MemoryUpdateCore

module_ports ports where
  input isLoad : .bit,
  input inputs (schema := DatapathInputs.schema) : inputsType,
  input current (schema := DatapathState.schema) : stateType,
  input updated (schema := DatapathState.schema) : stateType,
  output state (schema := DatapathState.schema) : stateType

def outputState (inputs : inputMap.Values) : stateMap.Values :=
  memoryNextState (inputs .isLoad) (Inputs.unpack (inputs .inputs))
    (stateMap.unpack (inputs .current))
    (stateMap.unpack (inputs .updated))

def outputRule : Silean.Contracts.Cycle.CycleOutputRule ports emptySignalMap where
  readsInputs := .all inputMap
  writesOutputs := .all outputMap
  target inputs _ := fun | .state => stateMap.pack (outputState inputs)

module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule apply := outputRule
  state_rule := Silean.Contracts.Cycle.CycleStateRule.empty _

@[simp] theorem outputRule_holds_iff (inputs : inputMap.Values)
    (state : emptySignalMap.Values) (outputs : outputMap.Values) :
    outputRule.Holds inputs state outputs ↔
      outputs .state = stateMap.pack (outputState inputs) := by
  simp only [Silean.Contracts.Cycle.CycleOutputRule.Holds, outputRule,
    Silean.SignalGroup.all_matches]
  constructor
  · intro equal; exact congrFun equal .state
  · intro equal; funext output; cases output; exact equal

end MemoryUpdateCore

namespace Baseline

module_ports ports where
  input current (schema := DatapathState.schema) : stateType,
  input alu_out : .vector 32 .bit,
  output state (schema := DatapathState.schema) : stateType

def outputState (inputs : inputMap.Values) : stateMap.Values :=
  baselineState (inputs .alu_out) (stateMap.unpack (inputs .current))

def outputRule : Silean.Contracts.Cycle.CycleOutputRule ports emptySignalMap where
  readsInputs := .all inputMap
  writesOutputs := .all outputMap
  target inputs _ := fun | .state => stateMap.pack (outputState inputs)

module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule apply := outputRule
  state_rule := Silean.Contracts.Cycle.CycleStateRule.empty _

@[simp] theorem outputRule_holds_iff (inputs : inputMap.Values)
    (state : emptySignalMap.Values) (outputs : outputMap.Values) :
    outputRule.Holds inputs state outputs ↔
      outputs .state = stateMap.pack (outputState inputs) := by
  simp only [Silean.Contracts.Cycle.CycleOutputRule.Holds, outputRule,
    Silean.SignalGroup.all_matches]
  constructor
  · intro equal; exact congrFun equal .state
  · intro equal; funext output; cases output; exact equal

end Baseline

namespace ResetOverride

module_ports ports where
  input resetn : .bit,
  input selected (schema := DatapathState.schema) : stateType,
  output state (schema := DatapathState.schema) : stateType

def outputState (inputs : inputMap.Values) : stateMap.Values :=
  resetApplied (inputs .resetn) (stateMap.unpack (inputs .selected))

def outputRule : Silean.Contracts.Cycle.CycleOutputRule ports emptySignalMap where
  readsInputs := .all inputMap
  writesOutputs := .all outputMap
  target inputs _ := fun | .state => stateMap.pack (outputState inputs)

module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule apply := outputRule
  state_rule := Silean.Contracts.Cycle.CycleStateRule.empty _

@[simp] theorem outputRule_holds_iff (inputs : inputMap.Values)
    (state : emptySignalMap.Values) (outputs : outputMap.Values) :
    outputRule.Holds inputs state outputs ↔
      outputs .state = stateMap.pack (outputState inputs) := by
  simp only [Silean.Contracts.Cycle.CycleOutputRule.Holds, outputRule,
    Silean.SignalGroup.all_matches]
  constructor
  · intro equal; exact congrFun equal .state
  · intro equal; funext output; cases output; exact equal

end ResetOverride

namespace Next

module_ports ports where
  input inputs (schema := DatapathInputs.schema) : inputsType,
  input current (schema := DatapathState.schema) : stateType,
  input alu_out : .vector 32 .bit,
  output state (schema := DatapathState.schema) : stateType

def outputState (inputs : inputMap.Values) : stateMap.Values :=
  nextStateFromAlu (Inputs.unpack (inputs .inputs))
    (stateMap.unpack (inputs .current)) (inputs .alu_out)

def outputRule : Silean.Contracts.Cycle.CycleOutputRule ports emptySignalMap where
  readsInputs := .all inputMap
  writesOutputs := .all outputMap
  target inputs _ := fun | .state => stateMap.pack (outputState inputs)

module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule apply := outputRule
  state_rule := Silean.Contracts.Cycle.CycleStateRule.empty _

@[simp] theorem outputRule_holds_iff (inputs : inputMap.Values)
    (state : emptySignalMap.Values) (outputs : outputMap.Values) :
    outputRule.Holds inputs state outputs ↔
      outputs .state = stateMap.pack (outputState inputs) := by
  simp only [Silean.Contracts.Cycle.CycleOutputRule.Holds, outputRule,
    Silean.SignalGroup.all_matches]
  constructor
  · intro equal; exact congrFun equal .state
  · intro equal; funext output; cases output; exact equal

end Next

end PicoRV.Datapath
