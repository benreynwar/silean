import PicoRV.ControlContract
import PicoRV.Authoring.CircuitLogic
import Silean.Authoring.ModuleCycleContract
import Silean.Modules.Constant.Constant

namespace PicoRV.Control

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring
open scoped Silean.Authoring

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

theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs .state = stateMap.pack (outputState step.inputs) :=
  (outputRule_holds_iff step.inputs step.currentState step.outputs).mp
    (allowed.1 .apply)

/-! The baseline layer represents the unconditional assignments at the start
of the source control block. Every state field passes through except `trap`
and `decoder_pseudo_trigger`, which clear, and `decoder_trigger`, which records
completion of the current instruction fetch. Later phase children deliberately
receive this result rather than the raw state. The expanded typed hierarchy
and verification remain under `Internal/`. -/

open ports

noncomputable def construction : ModuleBuilder ports Unit := do
  let inputs ← input .inputs
  let current ← input .current
  let inputsFields ← split ControlInputs.layout inputs
  let currentFields ← split ControlState.layout current
  let falseBit ← constant .bit false
  wire fetchCompleted : .bit ←
    currentFields .mem_do_rinst &&& inputsFields .mem_done
  let result ← update stateMap ControlState.schema currentFields fun
    | .decoder_trigger => some fetchCompleted
    | .decoder_pseudo_trigger | .trap => some falseBit
    | _ => none
  output .state result

noncomputable def description : Description :=
  ModuleBuilder.build Naming.ports construction

end Baseline

end PicoRV.Control
