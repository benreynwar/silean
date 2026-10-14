import Silean.Authoring.CircuitDescriptionSoundness
import Silean.Authoring.CircuitDescriptionContracts
import Silean.Modules.Fifo.FifoPointerControl
import Silean.Modules.Fifo.Internal.FifoPointerControlVerification

/-! Checked correspondence between the reader-facing FIFO pointer-control
description and its expanded typed production structure. This is separate from
cycle verification so the two independent checks remain small compilation
units. -/

namespace Silean.Modules.Fifo.PointerControl.Internal

open Silean Naming Authoring.CircuitDescription

private theorem same (addressWidth : Nat) :
  some (PointerControl.description addressWidth) =
      ofNaming (PointerControl.naming addressWidth) := by
  simp only [circuit_description, description, construction,
    PointerControl.pointerSplitter, PointerControl.addressCombiner]
  simp [circuit_description, enumeration]
  rfl

theorem description_corresponds (addressWidth : Nat) :
    Corresponds (PointerControl.description addressWidth)
      (PointerControl.naming addressWidth) :=
  ⟨same addressWidth⟩

open Authoring.CircuitDescription.Description

theorem construction_correct (addressWidth : Nat) :
    ImplementsCycleContract (PointerControl.description addressWidth)
      (cycleContract addressWidth) (Naming.ports addressWidth) := by
  have corresponds := description_corresponds addressWidth
  unfold PointerControl.naming at corresponds
  simp only [id_eq] at corresponds
  exact ImplementsCycleContract.of_certification
    (referenceBody := {
      instancePorts := instancePorts addressWidth,
      wiring := wiring addressWidth })
    (children := structuralChildren addressWidth)
    corresponds (certification addressWidth)

end Silean.Modules.Fifo.PointerControl.Internal
