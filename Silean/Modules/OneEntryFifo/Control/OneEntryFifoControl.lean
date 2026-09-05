import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModuleDesign
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.EqPrimitive
import Silean.Primitives.NotPrimitive
import Silean.Primitives.OrPrimitive

namespace Silean.Modules.OneEntryFifo

open Silean
open Silean.Authoring

/-! Combinational handshake control for a fall-through one-entry FIFO. -/

module_design Control where
  ports {
    input storedValid : .bit,
    input downstreamReady : .bit,
    output upstreamReady : .bit,
    output storageUpdate : .bit }
  instances {
    -- Detects that the storage entry is empty.
    invertValid := Primitives.notDesign,
    -- Makes the upstream ready when storage is empty or downstream is ready.
    readyOr := Primitives.orDesign,
    -- Detects the two cases in which the storage-valid bit must change.
    updateEq := Primitives.eqDesign }
  wiring {
    outputs {
      .upstreamReady := readyOr.output,
      .storageUpdate := updateEq.output }
    instance (.invertValid) {
      .input := input.storedValid }
    instance (.readyOr) {
      .left := input.downstreamReady,
      .right := invertValid.output }
    instance (.updateEq) {
      .left := input.downstreamReady,
      .right := input.storedValid }
  }

end Silean.Modules.OneEntryFifo

namespace Silean.Modules.OneEntryFifo.Control

open Silean
open Silean.Authoring

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

end Silean.Modules.OneEntryFifo.Control
