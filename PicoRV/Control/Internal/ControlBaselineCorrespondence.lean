import PicoRV.Control.ControlBaseline
import PicoRV.Control.Internal.ControlBaselineStructure
import Silean.Authoring.CircuitDescriptionSoundness

namespace PicoRV.Control.Baseline.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming Baseline.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold Baseline.moduleStructure Baseline.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [Baseline.body, Baseline.context, Baseline.instancePorts,
    Baseline.structuralChildren, Baseline.wiring, sourceDescription,
    Silean.Modules.Constant.design, EndpointContext.moduleInput,
    EndpointContext.instanceOutput]
  simp [circuit_description, enumeration]
  rfl

theorem description_corresponds : Corresponds description Baseline.naming :=
  ⟨same⟩

end PicoRV.Control.Baseline.Internal
