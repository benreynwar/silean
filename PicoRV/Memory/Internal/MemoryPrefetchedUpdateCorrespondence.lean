import PicoRV.Memory.MemoryBasicUpdates
import Silean.Authoring.CircuitDescriptionSoundness

namespace PicoRV.Memory.PrefetchedUpdate.Description.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming PrefetchedUpdate.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold PrefetchedUpdate.moduleStructure PrefetchedUpdate.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [PrefetchedUpdate.body, PrefetchedUpdate.context,
    PrefetchedUpdate.instancePorts, PrefetchedUpdate.structuralChildren,
    PrefetchedUpdate.wiring, sourceDescription, EndpointContext.moduleInput,
    EndpointContext.instanceOutput]
  simp [circuit_description, enumeration]

theorem corresponds : Corresponds description PrefetchedUpdate.naming :=
  ⟨same⟩

end PicoRV.Memory.PrefetchedUpdate.Description.Internal
