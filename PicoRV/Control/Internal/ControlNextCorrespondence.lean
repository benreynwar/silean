import PicoRV.Control.ControlNext
import PicoRV.Control.Internal.ControlNextStructure
import Silean.Authoring.CircuitDescriptionSoundness

/-! Checked correspondence between the reader-facing complete control update
and its expanded typed production structure. -/

namespace PicoRV.Control.ControlNext.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming ControlNext.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold ControlNext.moduleStructure ControlNext.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [ControlNext.body, ControlNext.context, ControlNext.instancePorts,
    ControlNext.structuralChildren, ControlNext.wiring, sourceDescription,
    EndpointContext.moduleInput, EndpointContext.instanceOutput]
  simp [circuit_description, enumeration, childId, Enumeration.ordinal]
  repeat' apply And.intro
  all_goals rfl

theorem description_corresponds : Corresponds description ControlNext.naming :=
  ⟨same⟩

end PicoRV.Control.ControlNext.Internal
