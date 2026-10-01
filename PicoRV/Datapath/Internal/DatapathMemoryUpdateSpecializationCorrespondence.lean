import PicoRV.Datapath.DatapathMemoryUpdate
import Silean.Authoring.CircuitDescriptionSoundness

namespace PicoRV.Datapath

open Silean Silean.Naming Silean.Authoring.CircuitDescription

namespace StoreUpdate.Description.Internal

private theorem same : some description = ofNaming StoreUpdate.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold StoreUpdate.moduleStructure StoreUpdate.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [StoreUpdate.body, StoreUpdate.context, StoreUpdate.instancePorts,
    StoreUpdate.structuralChildren, StoreUpdate.wiring, sourceDescription,
    EndpointContext.moduleInput, EndpointContext.instanceOutput]
  simp [circuit_description, enumeration]

theorem corresponds : Corresponds description StoreUpdate.naming :=
  ⟨same⟩

end StoreUpdate.Description.Internal

namespace LoadUpdate.Description.Internal

private theorem same : some description = ofNaming LoadUpdate.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold LoadUpdate.moduleStructure LoadUpdate.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [LoadUpdate.body, LoadUpdate.context, LoadUpdate.instancePorts,
    LoadUpdate.structuralChildren, LoadUpdate.wiring, sourceDescription,
    EndpointContext.moduleInput, EndpointContext.instanceOutput]
  simp [circuit_description, enumeration]

theorem corresponds : Corresponds description LoadUpdate.naming :=
  ⟨same⟩

end LoadUpdate.Description.Internal

end PicoRV.Datapath
