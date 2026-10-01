import PicoRV.Internal.RegsStructure
import Silean.Authoring.CircuitDescriptionSoundness

/-! Checked correspondence between the reader-facing register-file circuit
and its expanded typed production structure. -/

namespace PicoRV.Regs.Internal

open Silean Silean.Naming Silean.Authoring.CircuitDescription

private theorem same : some description = ofNaming Regs.naming := by
  simp only [circuit_description, description, construction,
    Silean.Modules.RegisterBank.place]
  simp only [show (inferInstance : Enumeration
      (Silean.Modules.RegisterBank.Input 2)).values =
    [.writeEnable, .writeAddress, .writeValue, .readAddress 0, .readAddress 1]
      by rfl]
  simp [circuit_description, enumeration]
  unfold Regs.moduleStructure Regs.naming
  simp only [id_eq]
  rw [ofNaming_composite]
  unfold ofCompositeNaming portList
  simp only [enumeration, List.map_cons, List.map_nil]
  dsimp [Regs.body, Regs.context, Regs.instancePorts,
    Regs.structuralChildren, Regs.wiring, sourceDescription,
    EndpointContext.moduleInput, EndpointContext.instanceOutput]
  simp only [show (inferInstance : Enumeration
      (Silean.Modules.RegisterBank.Input 2)).values =
    [.writeEnable, .writeAddress, .writeValue, .readAddress 0, .readAddress 1]
      by rfl]
  simp [circuit_description, enumeration, childId, Enumeration.ordinal]
  exact of_decide_eq_true rfl

theorem description_corresponds : Corresponds description Regs.naming :=
  ⟨same⟩

end PicoRV.Regs.Internal
