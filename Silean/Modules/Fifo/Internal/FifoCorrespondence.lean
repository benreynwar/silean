import Silean.Authoring.CircuitDescriptionSoundness
import Silean.Modules.Fifo.Fifo

/-! Checked correspondence between the reader-facing FIFO description and its
expanded typed production structure. Kept separate from cycle verification so
the structural translation check remains an independent, small compilation
unit. -/

namespace Silean.Modules.Fifo.Description.Internal

open Silean Naming Authoring.CircuitDescription

private theorem same (element : SignalType) (addressWidth : Nat) :
    some (description element addressWidth) =
      ofNaming (Fifo.naming element addressWidth) := by
  simp only [circuit_description, description, construction,
    EnabledResetCounter.placeNamed, PointerControl.place,
    RegisterBank.place, EnabledResetCounter.design]
  simp only [show (inferInstance : Enumeration (RegisterBank.Input 1)).values =
    [.writeEnable, .writeAddress, .writeValue, .readAddress 0] by rfl]
  simp [circuit_description, enumeration]
  rfl

private theorem unique (element : SignalType) (addressWidth : Nat) :
    (description element addressWidth).UniqueNames := by
  simp only [circuit_description, description, construction,
    EnabledResetCounter.placeNamed, PointerControl.place,
    RegisterBank.place, EnabledResetCounter.design]
  simp only [show (inferInstance : Enumeration (RegisterBank.Input 1)).values =
    [.writeEnable, .writeAddress, .writeValue, .readAddress 0] by rfl]
  simp [circuit_description, enumeration]
  refine ⟨of_decide_eq_true rfl, of_decide_eq_true rfl, ?_⟩
  intro child member
  change child ∈ [_, _, _, _] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal | equal | equal <;>
    subst child <;> constructor <;> exact of_decide_eq_true rfl

theorem corresponds (element : SignalType) (addressWidth : Nat) :
    Corresponds (description element addressWidth)
      (Fifo.naming element addressWidth) :=
  ⟨same element addressWidth, unique element addressWidth⟩

end Silean.Modules.Fifo.Description.Internal
