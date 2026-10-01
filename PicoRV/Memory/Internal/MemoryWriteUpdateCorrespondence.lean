import PicoRV.Memory.MemoryBasicUpdates
import Silean.Authoring.CircuitDescriptionSoundness

namespace PicoRV.Memory.WriteUpdate.Description.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming WriteUpdate.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold WriteUpdate.moduleStructure WriteUpdate.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [WriteUpdate.body, WriteUpdate.context, WriteUpdate.instancePorts,
    WriteUpdate.structuralChildren, WriteUpdate.wiring, sourceDescription,
    EndpointContext.moduleInput, EndpointContext.instanceOutput]
  simp [circuit_description, enumeration]

theorem corresponds : Corresponds description WriteUpdate.naming :=
  ⟨same⟩

end PicoRV.Memory.WriteUpdate.Description.Internal
