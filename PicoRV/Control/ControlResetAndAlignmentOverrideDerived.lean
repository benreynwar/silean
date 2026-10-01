import PicoRV.Control.Internal.ControlResetAndAlignmentOverrideVerification

/-! Public reset/alignment declarations backed by generated internals. -/

namespace PicoRV.Control.ResetAndAlignmentOverride

open Silean
open Silean.Authoring.CircuitDescription

structure PlacedOutputs where
  transition : Net transitionType

noncomputable def placeNamed (name : Naming.SourceName)
    (inputs : Net inputsType) (current baseline : Net stateType)
    (selected : Net transitionType) : Builder PlacedOutputs := do
  let child ← Authoring.CircuitDescription.placeNamed name design fun
    | .inputs => inputs
    | .current => current
    | .baseline => baseline
    | .selected => selected
  pure ⟨child .transition⟩

noncomputable def place (inputs : Net inputsType)
    (current baseline : Net stateType) (selected : Net transitionType) :
    Builder PlacedOutputs := do
  let child ← placeIndexed "reset_alignment_override" design fun
    | .inputs => inputs
    | .current => current
    | .baseline => baseline
    | .selected => selected
  pure ⟨child .transition⟩

attribute [circuit_description] placeNamed place

theorem construction_correct :
    description.ImplementsCycleContract cycleContract Naming.ports :=
  Internal.construction_correct

theorem implements_contract :
    Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨certified.certification.structural.hasSolution, certified.certification.structural.hasAtMostOneSolution⟩


end PicoRV.Control.ResetAndAlignmentOverride
