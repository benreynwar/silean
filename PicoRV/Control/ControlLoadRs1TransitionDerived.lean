import PicoRV.Control.Internal.ControlLoadRs1TransitionVerification

namespace PicoRV.Control.LoadRs1Transition

open Silean
open Silean.Authoring.CircuitDescription

structure PlacedOutputs where
  transition : Net transitionType

noncomputable def placeNamed (name : Naming.SourceName)
    (inputs : Net inputsType) (current updated : Net stateType) :
    Builder PlacedOutputs := do
  let child ← Authoring.CircuitDescription.placeNamed name design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure ⟨child .transition⟩

noncomputable def place (inputs : Net inputsType)
    (current updated : Net stateType) : Builder PlacedOutputs := do
  let child ← placeIndexed "load_rs1_transition" design fun
    | .inputs => inputs
    | .current => current
    | .updated => updated
  pure ⟨child .transition⟩

attribute [circuit_description] placeNamed place

theorem construction_correct :
    description.ImplementsCycleContract cycleContract
      PhaseTransition.Naming.ports := Internal.construction_correct

theorem implements_contract :
    Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds := certification.implements

theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨certified.certification.structural.hasSolution, certified.certification.structural.hasAtMostOneSolution⟩


end PicoRV.Control.LoadRs1Transition
