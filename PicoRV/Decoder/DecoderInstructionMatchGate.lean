import Silean.Authoring.CircuitDescriptionContracts
import Silean.Authoring.CircuitLogic
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts

/-! # Instruction-match gate

One exact instruction predicate is the conjunction of its broad opcode class,
field match, and optional qualifier.
-/

namespace PicoRV.Decoder.InstructionMatch.MatchGate

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open scoped Silean.Authoring

module_ports ports where
  input broad : .bit,
  input field : .bit,
  input qualifier : .bit,
  output result : .bit

open ports

noncomputable def construction : ModuleBuilder ports Unit := do
  let broad ← input .broad
  let field ← input .field
  let qualifier ← input .qualifier
  output .result (← (← broad &&& field) &&& qualifier)

noncomputable def description : Description :=
  ModuleBuilder.build Naming.ports construction

module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule apply where
    reads := [broad, field, qualifier]
    writes := { result := (broad && field) && qualifier }
  state_rule where
    reads := []
    next := {}

/-- Every allowed step returns the conjunction of all three conditions. -/
theorem result_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs .result =
      ((step.inputs .broad && step.inputs .field) && step.inputs .qualifier) :=
  cycleContract.result allowed

end PicoRV.Decoder.InstructionMatch.MatchGate
