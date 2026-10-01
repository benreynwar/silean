import PicoRV.Memory.MemoryBasicUpdates
import Silean.Authoring.CircuitDescriptionSoundness

namespace PicoRV.Memory.ResetTrapOverride.Description.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming ResetTrapOverride.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold ResetTrapOverride.moduleStructure ResetTrapOverride.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [ResetTrapOverride.body, ResetTrapOverride.context,
    ResetTrapOverride.instancePorts, ResetTrapOverride.structuralChildren,
    ResetTrapOverride.wiring, sourceDescription, EndpointContext.moduleInput,
    EndpointContext.instanceOutput]
  simp [circuit_description, enumeration]

theorem corresponds : Corresponds description ResetTrapOverride.naming :=
  ⟨same⟩

end PicoRV.Memory.ResetTrapOverride.Description.Internal
