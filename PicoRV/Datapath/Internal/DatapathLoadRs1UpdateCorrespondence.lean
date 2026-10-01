import PicoRV.Datapath.DatapathLoadRs1Update
import Silean.Authoring.CircuitDescriptionSoundness

namespace PicoRV.Datapath.LoadRs1Update.Description.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming LoadRs1Update.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold LoadRs1Update.moduleStructure LoadRs1Update.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [LoadRs1Update.body, LoadRs1Update.context,
    LoadRs1Update.instancePorts, LoadRs1Update.structuralChildren,
    LoadRs1Update.wiring, sourceDescription, EndpointContext.moduleInput,
    EndpointContext.instanceOutput]
  simp [circuit_description, enumeration]

theorem corresponds : Corresponds description LoadRs1Update.naming :=
  ⟨same⟩

end PicoRV.Datapath.LoadRs1Update.Description.Internal
