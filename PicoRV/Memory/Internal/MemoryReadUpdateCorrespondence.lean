import PicoRV.Memory.MemoryBasicUpdates
import Silean.Authoring.CircuitDescriptionSoundness

namespace PicoRV.Memory.ReadUpdate.Description.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming ReadUpdate.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold ReadUpdate.moduleStructure ReadUpdate.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [ReadUpdate.body, ReadUpdate.context, ReadUpdate.instancePorts,
    ReadUpdate.structuralChildren, ReadUpdate.wiring, sourceDescription,
    EndpointContext.moduleInput, EndpointContext.instanceOutput]
  simp [circuit_description, enumeration]

theorem corresponds : Corresponds description ReadUpdate.naming :=
  ⟨same⟩

end PicoRV.Memory.ReadUpdate.Description.Internal
