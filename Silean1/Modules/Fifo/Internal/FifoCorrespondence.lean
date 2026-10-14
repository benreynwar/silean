import Silean.Authoring.CircuitDescriptionSoundness
import Silean.Authoring.CircuitDescriptionContracts
import Silean.Modules.Fifo.Fifo
import Silean.Modules.Fifo.Internal.FifoCycleVerification

/-! Checked correspondence between the reader-facing FIFO description and its
expanded typed production structure. Kept separate from cycle verification so
the structural translation check remains an independent, small compilation
unit. -/

namespace Silean.Modules.Fifo.Internal

open Silean Naming Authoring.CircuitDescription

private theorem same (element : SignalType) (addressWidth : Nat) :
    some (Fifo.description element addressWidth) =
      ofNaming (Fifo.naming element addressWidth) := by
  simp only [circuit_description, description, construction,
    EnabledResetCounter.placeNamed, PointerControl.place,
    RegisterBank.place]
  simp only [show (inferInstance : Enumeration (RegisterBank.Input 1)).values =
    [.writeEnable, .writeAddress, .writeValue, .readAddress 0] by rfl]
  simp [circuit_description, enumeration]
  rfl

theorem description_corresponds (element : SignalType) (addressWidth : Nat) :
    Corresponds (Fifo.description element addressWidth)
      (Fifo.naming element addressWidth) :=
  ⟨same element addressWidth⟩

open Authoring.CircuitDescription.Description

theorem construction_correct (element : SignalType) (addressWidth : Nat) :
    ImplementsCycleContract (Fifo.description element addressWidth)
      (cycleContract element addressWidth)
      (Naming.FifoPorts.ports element) := by
  have corresponds := description_corresponds element addressWidth
  unfold Fifo.naming at corresponds
  simp only [id_eq] at corresponds
  exact ImplementsCycleContract.of_certification
    (referenceBody := {
      instancePorts := instancePorts element addressWidth,
      wiring := wiring element addressWidth })
    (children := structuralChildren element addressWidth)
    corresponds (certification element addressWidth)

end Silean.Modules.Fifo.Internal
