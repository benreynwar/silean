import PicoRV.Memory.MemoryBasicUpdates
import Silean.Authoring.CircuitDescriptionSoundness

namespace PicoRV.Memory.ResponseCapture.Description.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming ResponseCapture.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold ResponseCapture.moduleStructure ResponseCapture.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [ResponseCapture.body, ResponseCapture.context,
    ResponseCapture.instancePorts, ResponseCapture.structuralChildren,
    ResponseCapture.wiring, sourceDescription, EndpointContext.moduleInput,
    EndpointContext.instanceOutput]

theorem corresponds : Corresponds description ResponseCapture.naming :=
  ⟨same⟩

end PicoRV.Memory.ResponseCapture.Description.Internal
