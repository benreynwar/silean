import Silean.Contracts.Cycle.CycleBlackbox
import PicoRV.ControlContract

namespace PicoRV.Control

open Silean
open Silean.Authoring

/-! Contracts for the combinational children used to construct
`PicoRVControlNext`. Each boundary speaks in the named aggregate types from
`ControlContract.lean`; packing is representation, while the contract result is one of
the source-level transition functions. -/

namespace PhaseDecode

module_ports ports where
  input cpu_state : .vector 8 .bit,
  output trap : .bit,
  output fetch : .bit,
  output loadRs1 : .bit,
  output loadRs2 : .bit,
  output execute : .bit,
  output shift : .bit,
  output store : .bit,
  output load : .bit

def outputValues (inputs : inputMap.Values) : outputMap.Values
  | .trap => decide (Silean.BitVector.toNat 8 (inputs .cpu_state) = cpuStateTrap)
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

/-! All eight phase children deliberately share this boundary. `inputs` is a
coarse dependency, but it is not a scheduling restriction: the enclosing
next-state computation already consumes the complete input tuple. `current`
is the pre-edge state and `updated` is the state after baseline assignments. -/

namespace PhaseTransition

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

end PhaseTransition

def trapTransitionChild (_ : Inputs) (_ : stateMap.Values)
    (updated : stateMap.Values) : Transition :=
  simpleTransition (stateMap.set updated .trap true)

namespace TrapTransition
abbrev cycleContract := PhaseTransition.cycleContract trapTransitionChild
end TrapTransition

namespace FetchTransition
abbrev cycleContract := PhaseTransition.cycleContract fetchTransition
end FetchTransition

namespace LoadRs1Transition
abbrev cycleContract := PhaseTransition.cycleContract
  (fun inputs _ updated => loadRs1Transition inputs updated)
end LoadRs1Transition

namespace LoadRs2Transition
abbrev cycleContract := PhaseTransition.cycleContract
  (fun inputs _ updated => loadRs2Transition inputs updated)
end LoadRs2Transition

namespace ExecuteTransition
abbrev cycleContract := PhaseTransition.cycleContract
  (fun inputs _ updated => executeTransition inputs updated)
end ExecuteTransition

namespace ShiftTransition
abbrev cycleContract := PhaseTransition.cycleContract
  (fun inputs _ updated => shiftTransition inputs updated)
end ShiftTransition

namespace StoreTransition
abbrev cycleContract := PhaseTransition.cycleContract storeTransition
end StoreTransition

namespace LoadTransition
abbrev cycleContract := PhaseTransition.cycleContract loadTransition
end LoadTransition

namespace Baseline

module_ports ports where
  input inputs (schema := ControlInputs.schema) : inputsType,
  input current (schema := ControlState.schema) : stateType,
  output state (schema := ControlState.schema) : stateType

def outputState (inputs : inputMap.Values) : stateMap.Values :=
  baselineState (Inputs.unpack (inputs .inputs))
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

end Baseline

namespace Alignment

module_ports ports where
  input inputs (schema := ControlInputs.schema) : inputsType,
  input current (schema := ControlState.schema) : stateType,
  output data : .bit,
  output instruction : .bit

def outputValues (inputs : inputMap.Values) : outputMap.Values :=
  let controlInputs := Inputs.unpack (inputs .inputs)
  let current := stateMap.unpack (inputs .current)
  fun
  | .data => dataMisaligned controlInputs current
  | .instruction => instructionMisaligned controlInputs current

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

end Alignment

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

end ResetAndAlignmentOverride

namespace ControlNext

module_ports ports where
  input inputs (schema := ControlInputs.schema) : inputsType,
  input current (schema := ControlState.schema) : stateType,
  output state (schema := ControlState.schema) : stateType

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

end ControlNext

end PicoRV.Control
