import PicoRV.Datapath.DatapathShiftUpdate
import Silean.Authoring.CircuitDescriptionSoundness

namespace PicoRV.Datapath.ShiftUpdate.Description.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming ShiftUpdate.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold ShiftUpdate.moduleStructure ShiftUpdate.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [ShiftUpdate.body, ShiftUpdate.context, ShiftUpdate.instancePorts,
    ShiftUpdate.structuralChildren, ShiftUpdate.wiring, sourceDescription,
    EndpointContext.moduleInput, EndpointContext.instanceOutput]
  simp [circuit_description, enumeration]
  rfl

theorem corresponds : Corresponds description ShiftUpdate.naming :=
  ⟨same⟩

end PicoRV.Datapath.ShiftUpdate.Description.Internal
