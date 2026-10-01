import PicoRV.Datapath.DatapathBasicUpdates
import Silean.Authoring.CircuitDescriptionSoundness

namespace PicoRV.Datapath.PhaseDecode.Description.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming PhaseDecode.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold PhaseDecode.moduleStructure PhaseDecode.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [PhaseDecode.body, PhaseDecode.context, PhaseDecode.instancePorts,
    PhaseDecode.structuralChildren, PhaseDecode.wiring, sourceDescription,
    EndpointContext.moduleInput, EndpointContext.instanceOutput]
  simp [circuit_description, enumeration]
  rfl

theorem corresponds : Corresponds description PhaseDecode.naming :=
  ⟨same⟩

end PicoRV.Datapath.PhaseDecode.Description.Internal
