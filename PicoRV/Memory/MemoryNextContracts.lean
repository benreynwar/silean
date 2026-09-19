import PicoRV.MemoryContract

namespace PicoRV.Memory

open Silean
open Silean.Authoring

/-! Combinational contracts used to construct `PicoRVMemoryNext`. Each
aggregate result is stated directly using the natural transition functions in
`MemoryContract.lean`; the structural children implement the source assignment
layers. -/

namespace ResponseCapture

module_ports ports where
  input inputs (schema := MemoryInputs.schema) : inputsType,
  input current (schema := MemoryState.schema) : stateType,
  output state (schema := MemoryState.schema) : stateType

def outputState (inputs : inputMap.Values) : stateMap.Values :=
  responseCaptured (Inputs.unpack (inputs .inputs))
    (stateMap.unpack (inputs .current))

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

end ResponseCapture

namespace StateUpdate

module_ports ports where
  input inputs (schema := MemoryInputs.schema) : inputsType,
  input current (schema := MemoryState.schema) : stateType,
  input updated (schema := MemoryState.schema) : stateType,
  output state (schema := MemoryState.schema) : stateType

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

namespace LookaheadCapture
abbrev cycleContract := StateUpdate.cycleContract lookaheadCaptured
end LookaheadCapture

namespace IdleUpdate
abbrev cycleContract := StateUpdate.cycleContract
  (fun inputs _ updated => idleNextState inputs updated)
end IdleUpdate

namespace ReadUpdate
abbrev cycleContract := StateUpdate.cycleContract readNextState
end ReadUpdate

namespace WriteUpdate
abbrev cycleContract := StateUpdate.cycleContract writeNextState
end WriteUpdate

namespace PrefetchedUpdate
abbrev cycleContract := StateUpdate.cycleContract
  (fun inputs _ updated => prefetchedNextState inputs updated)
end PrefetchedUpdate

namespace PhaseDecode

module_ports ports where
  input mem_state : .vector 2 .bit,
  output idle : .bit,
  output read : .bit,
  output write : .bit,
  output prefetched : .bit

def outputValues (inputs : inputMap.Values) : outputMap.Values
  | .idle => decide (Silean.BitVector.toNat 2 (inputs .mem_state) = 0)
  | .read => decide (Silean.BitVector.toNat 2 (inputs .mem_state) = 1)
  | .write => decide (Silean.BitVector.toNat 2 (inputs .mem_state) = 2)
  | .prefetched => decide (Silean.BitVector.toNat 2 (inputs .mem_state) = 3)

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

namespace ResetTrapOverride

module_ports ports where
  input inputs (schema := MemoryInputs.schema) : inputsType,
  input captured (schema := MemoryState.schema) : stateType,
  input normal (schema := MemoryState.schema) : stateType,
  output state (schema := MemoryState.schema) : stateType

def outputState (inputs : inputMap.Values) : stateMap.Values :=
  resetTrapApplied (Inputs.unpack (inputs .inputs))
    (stateMap.unpack (inputs .captured))
    (stateMap.unpack (inputs .normal))

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

end ResetTrapOverride

namespace Next

module_ports ports where
  input inputs (schema := MemoryInputs.schema) : inputsType,
  input current (schema := MemoryState.schema) : stateType,
  output state (schema := MemoryState.schema) : stateType

def outputState (inputs : inputMap.Values) : stateMap.Values :=
  nextState (Inputs.unpack (inputs .inputs))
    (stateMap.unpack (inputs .current))

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

end PicoRV.Memory
