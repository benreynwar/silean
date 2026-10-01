import PicoRV.Datapath.DatapathBasicUpdates
import Silean.Authoring.CircuitDescriptionSoundness

namespace PicoRV.Datapath.ResetOverride.Description.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming ResetOverride.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold ResetOverride.moduleStructure ResetOverride.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [ResetOverride.body, ResetOverride.context,
    ResetOverride.instancePorts, ResetOverride.structuralChildren,
    ResetOverride.wiring, sourceDescription, EndpointContext.moduleInput,
    EndpointContext.instanceOutput]
  simp [circuit_description, enumeration]

theorem corresponds : Corresponds description ResetOverride.naming :=
  ⟨same⟩

end PicoRV.Datapath.ResetOverride.Description.Internal
