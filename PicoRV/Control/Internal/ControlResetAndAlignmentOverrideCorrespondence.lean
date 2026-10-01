import PicoRV.Control.ControlResetAndAlignmentOverride
import PicoRV.Control.Internal.ControlResetAndAlignmentOverrideStructure
import Silean.Authoring.CircuitDescriptionSoundness

/-! Checked correspondence between the reader-facing reset/alignment override
and its expanded typed production structure. -/

namespace PicoRV.Control.ResetAndAlignmentOverride.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same :
    some description = ofNaming ResetAndAlignmentOverride.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  unfold ResetAndAlignmentOverride.moduleStructure
    ResetAndAlignmentOverride.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [ResetAndAlignmentOverride.body, ResetAndAlignmentOverride.context,
    ResetAndAlignmentOverride.instancePorts,
    ResetAndAlignmentOverride.structuralChildren,
    ResetAndAlignmentOverride.wiring, sourceDescription,
    EndpointContext.moduleInput, EndpointContext.instanceOutput]
  simp [circuit_description, enumeration, childId, Enumeration.ordinal]
  repeat' apply And.intro
  all_goals rfl

theorem description_corresponds :
    Corresponds description ResetAndAlignmentOverride.naming :=
  ⟨same⟩

end PicoRV.Control.ResetAndAlignmentOverride.Internal
