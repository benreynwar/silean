import Silean.Authoring.CircuitLogic
import Silean.Authoring.CircuitDescriptionContracts
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts

/-! # One-bit multiplexer

The authored circuit selects between two bits. Its contract states that
behavior independently of the four-gate implementation.
-/

namespace Silean.Modules.BitMux

open Silean
open Silean.Authoring
open Authoring.CircuitDescription
open scoped Authoring

module_ports ports where
  input select : .bit,
  input whenFalse : .bit,
  input whenTrue : .bit,
  output result : .bit

open ports

noncomputable def construction : ModuleBuilder ports Unit := do
  let select ← input .select
  let whenFalse ← input .whenFalse
  let whenTrue ← input .whenTrue
  output .result (←
    (← whenFalse &&& (← !! select)) ||| (← whenTrue &&& select))

noncomputable def description : Description :=
  ModuleBuilder.build Naming.ports construction

module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule select where
    reads := [select, whenFalse, whenTrue]
    writes := { result := bif select then whenTrue else whenFalse }
  state_rule where
    reads := []
    next := {}

end Silean.Modules.BitMux
