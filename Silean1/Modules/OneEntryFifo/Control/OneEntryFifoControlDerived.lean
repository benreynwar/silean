import Silean.Modules.OneEntryFifo.Control.Internal.OneEntryFifoControlVerification

/-! Public declarations backed by the generated one-entry FIFO control structure. -/

namespace Silean.Modules.OneEntryFifo.Control

open Silean
open Authoring.CircuitDescription

/-- Place the control child under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Naming.SourceName)
    (storedValid downstreamReady : Net .bit) : Builder ports.OutputNets :=
  ports.placeNamed name moduleStructure naming storedValid downstreamReady

/-- Place the control child using the next conventional indexed name. -/
noncomputable def place (storedValid downstreamReady : Net .bit) :
    Builder ports.OutputNets :=
  ports.placeIndexed "one_entry_fifo_control" moduleStructure naming
    storedValid downstreamReady

attribute [circuit_description] placeNamed place

/-- Every typed implementation corresponding to the authored construction
implements the control contract. -/
theorem construction_correct :
    description.ImplementsCycleContract cycleContract Naming.ports :=
  Internal.construction_correct

/-- The generated control hierarchy implements its exact cycle contract. -/
theorem implements_contract :
    Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

end Silean.Modules.OneEntryFifo.Control
