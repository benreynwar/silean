import PicoRV.ControlContract
import Silean.Authoring.CircuitDescription
import Silean.Authoring.ModuleCycleContract
import Silean.Modules.EqualsConstant.EqualsConstantDerived

namespace PicoRV.Control

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription

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

theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs = outputValues step.inputs :=
  (outputRule_holds_iff step.inputs step.currentState step.outputs).mp
    (allowed.1 .apply)

/-! Exact full-vector phase decoding. The eight comparisons are independent;
no one-hot or reachability assumption is built into the circuit. The expanded
typed hierarchy and its verification remain under `Internal/`. -/

open ports

noncomputable def construction : ModuleBuilder ports Unit := do
  let state ← input .cpu_state
  output .trap (← Silean.Modules.EqualsConstant.place
    state (stateBits cpuStateTrap))
  output .fetch (← Silean.Modules.EqualsConstant.place
    state (stateBits cpuStateFetch))
  output .loadRs1 (← Silean.Modules.EqualsConstant.place
    state (stateBits cpuStateLdRs1))
  output .loadRs2 (← Silean.Modules.EqualsConstant.place
    state (stateBits cpuStateLdRs2))
  output .execute (← Silean.Modules.EqualsConstant.place
    state (stateBits cpuStateExec))
  output .shift (← Silean.Modules.EqualsConstant.place
    state (stateBits cpuStateShift))
  output .store (← Silean.Modules.EqualsConstant.place
    state (stateBits cpuStateStmem))
  output .load (← Silean.Modules.EqualsConstant.place
    state (stateBits cpuStateLdmem))

noncomputable def description : Description :=
  ModuleBuilder.build Naming.ports construction

end PhaseDecode

end PicoRV.Control
