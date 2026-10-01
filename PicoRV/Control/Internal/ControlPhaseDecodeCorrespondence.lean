import PicoRV.Control.ControlPhaseDecode
import PicoRV.Control.Internal.ControlPhaseDecodeStructure
import Silean.Authoring.CircuitDescriptionSoundness

namespace PicoRV.Control.PhaseDecode.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming PhaseDecode.naming := by
  simp only [circuit_description, description, construction]
  simp [circuit_description, enumeration]
  rfl

theorem description_corresponds : Corresponds description PhaseDecode.naming :=
  ⟨same⟩

end PicoRV.Control.PhaseDecode.Internal
