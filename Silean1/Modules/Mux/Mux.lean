import Silean.Authoring.CircuitLogic
import Silean.Authoring.CircuitDescriptionContracts
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts

/-! # Multiplexer

The authored circuit selects between two equally shaped signals. Its contract
states that behavior independently of the gate-level implementation.
-/

namespace Silean.Modules.Mux

open Silean
open Silean.Authoring
open Authoring.CircuitDescription
open scoped Authoring

module_ports ports (signalType : SignalType)
    with (typeNaming : Naming.SignalTypeNaming signalType :=
      .positional signalType) where
  input select : .bit,
  input whenFalse (schema := typeNaming) : signalType,
  input whenTrue (schema := typeNaming) : signalType,
  output result (schema := typeNaming) : signalType

open ports

noncomputable def construction (signalType : SignalType) :
    ModuleBuilder (ports signalType) Unit := do
  let select ← input signalType .select
  let whenFalse ← input signalType .whenFalse
  let whenTrue ← input signalType .whenTrue
  output signalType .result (←
    (← whenFalse &&& (← !! select)) ||| (← whenTrue &&& select))

noncomputable def description (signalType : SignalType) : Description :=
  ModuleBuilder.build (Naming.ports signalType) (construction signalType)

module_cycle_contract cycleContract (signalType : SignalType)
    for ports signalType where
  state := emptySignalMap
  output_rule select where
    reads := [select, whenFalse, whenTrue]
    writes := {
      result := bif select then whenTrue else whenFalse }
  state_rule where
    reads := []
    next := {}

end Silean.Modules.Mux
