import PicoRV.Datapath.DatapathMemoryUpdate
import Silean.Authoring.CircuitDescriptionSoundness

namespace PicoRV.Datapath.MemoryUpdateCore.Description.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming MemoryUpdateCore.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold MemoryUpdateCore.moduleStructure MemoryUpdateCore.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [MemoryUpdateCore.body, MemoryUpdateCore.context,
    MemoryUpdateCore.instancePorts, MemoryUpdateCore.structuralChildren,
    MemoryUpdateCore.wiring, sourceDescription, EndpointContext.moduleInput,
    EndpointContext.instanceOutput]
  simp [circuit_description, enumeration]

theorem corresponds : Corresponds description MemoryUpdateCore.naming :=
  ⟨same⟩

end PicoRV.Datapath.MemoryUpdateCore.Description.Internal
