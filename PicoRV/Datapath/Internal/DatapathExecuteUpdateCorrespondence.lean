import PicoRV.Datapath.DatapathBasicUpdates
import Silean.Authoring.CircuitDescriptionSoundness

namespace PicoRV.Datapath.ExecuteUpdate.Description.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming ExecuteUpdate.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold ExecuteUpdate.moduleStructure ExecuteUpdate.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [ExecuteUpdate.body, ExecuteUpdate.context,
    ExecuteUpdate.instancePorts, ExecuteUpdate.structuralChildren,
    ExecuteUpdate.wiring, sourceDescription, EndpointContext.moduleInput,
    EndpointContext.instanceOutput]
  simp [circuit_description, enumeration]
  rfl

theorem corresponds : Corresponds description ExecuteUpdate.naming :=
  ⟨same⟩

end PicoRV.Datapath.ExecuteUpdate.Description.Internal
