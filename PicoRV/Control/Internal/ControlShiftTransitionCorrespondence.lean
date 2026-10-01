import PicoRV.Control.ControlShiftTransition
import PicoRV.Control.Internal.ControlShiftTransitionStructure
import Silean.Authoring.CircuitDescriptionSoundness

/-! Checked correspondence between the reader-facing shift-transition
description and its expanded typed production structure. -/

namespace PicoRV.Control.ShiftTransition.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same :
    some description = ofNaming ShiftTransition.naming := by
  simp only [circuit_description, description, construction,
    Silean.Modules.EqualsConstant.place]
  simp [circuit_description, enumeration]
  unfold ShiftTransition.moduleStructure ShiftTransition.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [ShiftTransition.body, ShiftTransition.context,
    ShiftTransition.instancePorts, ShiftTransition.structuralChildren,
    ShiftTransition.wiring, sourceDescription,
    Silean.Modules.Constant.design,
    EndpointContext.moduleInput, EndpointContext.instanceOutput]
  simp [circuit_description, enumeration]
  rfl

theorem description_corresponds : Corresponds description ShiftTransition.naming :=
  ⟨same⟩

end PicoRV.Control.ShiftTransition.Internal
