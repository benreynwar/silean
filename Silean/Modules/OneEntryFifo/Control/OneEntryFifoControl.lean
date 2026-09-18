import Silean.Authoring.CircuitDescription
import Silean.Authoring.ModuleCycleContract
import Silean.Modules.OneEntryFifo.Control.Internal.OneEntryFifoControlStructure
import Silean.Primitives.Eq
import Silean.Primitives.Not
import Silean.Primitives.Or

/-! # One-entry FIFO control

This is the one-entry FIFO's private combinational handshake child. It makes
the upstream ready when the entry is empty or the downstream is ready, and it
requests a storage update exactly when downstream readiness and current
occupancy agree.

It is kept as a child because the same two decisions drive several independent
data-path elements in the parent. It is not intended as a general-purpose
public module.
-/

namespace Silean.Modules.OneEntryFifo.Control.Description

open Silean
open Silean.Authoring.CircuitDescription

noncomputable def construction : Builder Unit := do
  let storedValid ← input "storedValid" .bit
  let downstreamReady ← input "downstreamReady" .bit
  let empty ← Primitives.Not.placeNamed "invertValid" storedValid
  let upstreamReady ← Primitives.Or.placeNamed "readyOr" downstreamReady empty
  let storageUpdate ← Primitives.Eq.placeNamed "updateEq"
    downstreamReady storedValid
  output "upstreamReady" upstreamReady
  output "storageUpdate" storageUpdate

noncomputable def description : Description :=
  build construction

end Silean.Modules.OneEntryFifo.Control.Description

namespace Silean.Modules.OneEntryFifo.Control

open Silean
open Silean.Authoring
open Authoring.CircuitDescription

/-! ## Placement -/

/-- Place the FIFO control child under a caller-chosen instance name. The
result is `(upstreamReady, storageUpdate)`. -/
noncomputable def placeNamed (name : Silean.Naming.SourceName)
    (storedValid downstreamReady : Net .bit) :
    Builder (Net .bit × Net .bit) := do
  let child ← Authoring.CircuitDescription.placeNamed name design fun
    | .storedValid => storedValid
    | .downstreamReady => downstreamReady
  pure (child .upstreamReady, child .storageUpdate)

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

end Silean.Modules.OneEntryFifo.Control
