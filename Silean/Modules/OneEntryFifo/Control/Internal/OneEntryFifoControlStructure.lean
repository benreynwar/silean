import Silean.Authoring.ModuleDesign
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.EqPrimitive
import Silean.Primitives.NotPrimitive
import Silean.Primitives.OrPrimitive

/-! Expanded typed hierarchy for the one-entry FIFO's private control child. -/

namespace Silean.Modules.OneEntryFifo

open Silean
open Silean.Authoring

module_design Control where
  ports {
    input storedValid : .bit,
    input downstreamReady : .bit,
    output upstreamReady : .bit,
    output storageUpdate : .bit }
  instances {
    invertValid := Primitives.notDesign,
    readyOr := Primitives.orDesign,
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

namespace Silean.Modules.OneEntryFifo.Control.Internal

@[simp] theorem invertValid_instance_name :
    Control.Naming.instanceNames .invertValid = "invertValid" := rfl

@[simp] theorem readyOr_instance_name :
    Control.Naming.instanceNames .readyOr = "readyOr" := rfl

@[simp] theorem updateEq_instance_name :
    Control.Naming.instanceNames .updateEq = "updateEq" := rfl

end Silean.Modules.OneEntryFifo.Control.Internal
