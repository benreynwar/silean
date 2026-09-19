import PicoRV.Regs
import Silean.Authoring.CircuitDescriptionSoundness

/-! Checked correspondence between the reader-facing register-file circuit
and its expanded typed production structure. -/

namespace PicoRV.Regs.Description.Internal

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
  simp [circuit_description, enumeration]

private theorem unique : description.UniqueNames := by
  simp only [circuit_description, description, construction,
    Silean.Modules.RegisterBank.place]
  simp only [show (inferInstance : Enumeration
      (Silean.Modules.RegisterBank.Input 2)).values =
    [.writeEnable, .writeAddress, .writeValue, .readAddress 0, .readAddress 1]
      by rfl]
  simp [circuit_description, enumeration, Silean.Modules.Equality.design,
    Silean.Modules.Equality.Naming.naming_ports]
  refine ⟨of_decide_eq_true rfl, of_decide_eq_true rfl, ?_⟩
  intro child member
  change child ∈ [_, _, _, _, _, _, _, _, _, _, _] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal | equal | equal | equal | equal |
      equal | equal | equal | equal | equal
  · subst child
    constructor <;> exact of_decide_eq_true rfl
  · subst child
    constructor <;> exact of_decide_eq_true rfl
  · subst child
    constructor
    · exact Silean.Modules.Equality.Naming.portNames_nodup addressType
    · exact of_decide_eq_true rfl
  · subst child
    constructor <;> exact of_decide_eq_true rfl
  · subst child
    constructor <;> exact of_decide_eq_true rfl
  · subst child
    constructor <;> exact of_decide_eq_true rfl
  · subst child
    constructor <;> exact of_decide_eq_true rfl
  · subst child
    constructor
    · exact Silean.Modules.Equality.Naming.portNames_nodup addressType
    · exact of_decide_eq_true rfl
  · subst child
    constructor <;> exact of_decide_eq_true rfl
  · subst child
    constructor
    · exact Silean.Modules.Equality.Naming.portNames_nodup addressType
    · exact of_decide_eq_true rfl
  · subst child
    constructor <;> exact of_decide_eq_true rfl

theorem corresponds : Corresponds description Regs.naming :=
  ⟨same, unique⟩

end PicoRV.Regs.Description.Internal
