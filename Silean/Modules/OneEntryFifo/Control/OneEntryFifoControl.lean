import Silean.Authoring.CircuitLogic
import Silean.Authoring.CircuitDescriptionContracts
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts

/-! # One-entry FIFO control

This is the one-entry FIFO's private combinational handshake child. It makes
the upstream ready when the entry is empty or the downstream is ready, and it
requests a storage update exactly when downstream readiness and current
occupancy agree.

It is kept as a child because the same two decisions drive several independent
data-path elements in the parent. It is not intended as a general-purpose
public module.
-/

namespace Silean.Modules.OneEntryFifo.Control

open Silean
open Silean.Authoring
open Authoring.CircuitDescription
open scoped Authoring

module_ports ports where
  input storedValid : .bit,
  input downstreamReady : .bit,
  output upstreamReady : .bit,
  output storageUpdate : .bit

open ports

noncomputable def construction : ModuleBuilder ports Unit := do
  let storedValid ← input .storedValid
  let downstreamReady ← input .downstreamReady
  output .upstreamReady (← downstreamReady ||| (← !! storedValid))
  output .storageUpdate (← downstreamReady === storedValid)

noncomputable def description : Description :=
  ModuleBuilder.build Naming.ports construction

/-! ## Exact combinational behavior -/

module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule control where
    reads := [storedValid, downstreamReady]
    writes := {
      upstreamReady := downstreamReady || !storedValid,
      storageUpdate := (downstreamReady && storedValid) ||
        (!downstreamReady && !storedValid) }
  state_rule where
    reads := []
    next := {}

section AllowedStep

variable {step : cycleContract.Step}
  (allowed : cycleContract.Allows step)

include allowed

end AllowedStep

end Silean.Modules.OneEntryFifo.Control
