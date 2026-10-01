import PicoRV.ControlContract
import PicoRV.Authoring.CircuitLogic
import Silean.Authoring.ModuleCycleContract
import Silean.Modules.EqualsConstant.EqualsConstantDerived

namespace PicoRV.Control

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring
open scoped Silean.Authoring

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

theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs = outputValues step.inputs :=
  (outputRule_holds_iff step.inputs step.currentState step.outputs).mp
    (allowed.1 .apply)

/-! # Control-address alignment

Misalignment is determined entirely by the current request, its word size, and
the low address bits. The description intentionally exposes those low-bit
tests rather than implementing division or remainder hardware. The expanded
typed hierarchy and verification remain under `Internal/`. -/

open ports

noncomputable def construction : ModuleBuilder ports Unit := do
  let inputs ← input .inputs
  let current ← input .current
  let inputsFields ← split ControlInputs.layout inputs
  let stateFields ← split ControlState.layout current
  let op1Bits ← splitVector 32 .bit (inputsFields .reg_op1)
  let pcBits ← splitVector 32 .bit (inputsFields .reg_pc)
  let sizeIsWord ← Silean.Modules.EqualsConstant.place
    (stateFields .mem_wordsize) (twoBitsOfNat 0)
  let sizeIsHalf ← Silean.Modules.EqualsConstant.place
    (stateFields .mem_wordsize) (twoBitsOfNat 1)
  let dataCommand ← stateFields .mem_do_rdata ||| stateFields .mem_do_wdata
  let op1Low ← op1Bits 0 ||| op1Bits 1
  let pcLow ← pcBits 0 ||| pcBits 1
  let wordMisaligned ← sizeIsWord &&& op1Low
  let halfMisaligned ← sizeIsHalf &&& op1Bits 0
  let sizeMisaligned ← wordMisaligned ||| halfMisaligned
  output .data (← dataCommand &&& sizeMisaligned)
  output .instruction (← stateFields .mem_do_rinst &&& pcLow)

noncomputable def description : Description :=
  ModuleBuilder.build Naming.ports construction

end Alignment

end PicoRV.Control
