import PicoRV.Datapath.DatapathFetchUpdate
import Silean.Authoring.CircuitDescriptionSoundness

namespace PicoRV.Datapath.FetchUpdate.Description.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming FetchUpdate.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold FetchUpdate.moduleStructure FetchUpdate.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [FetchUpdate.body, FetchUpdate.context, FetchUpdate.instancePorts,
    FetchUpdate.structuralChildren, FetchUpdate.wiring, sourceDescription,
    EndpointContext.moduleInput, EndpointContext.instanceOutput]
  simp [circuit_description, enumeration]

theorem corresponds : Corresponds description FetchUpdate.naming :=
  ⟨same⟩

end PicoRV.Datapath.FetchUpdate.Description.Internal
