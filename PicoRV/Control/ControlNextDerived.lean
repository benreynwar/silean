import PicoRV.Control.Internal.ControlNextVerification

/-! Public complete-control declarations backed by generated internals. -/

namespace PicoRV.Control.ControlNext

open Silean
open Silean.Authoring.CircuitDescription

noncomputable def placeNamed (name : Naming.SourceName)
    (inputs : Net inputsType) (current : Net stateType) :
    Builder (Net stateType) := do
  let child ← Authoring.CircuitDescription.placeNamed name design fun
    | .inputs => inputs
    | .current => current
  pure (child .state)

noncomputable def place (inputs : Net inputsType) (current : Net stateType) :
    Builder (Net stateType) := do
  let child ← placeIndexed "control_next" design fun
    | .inputs => inputs
    | .current => current
  pure (child .state)

attribute [circuit_description] placeNamed place

theorem construction_correct :
    description.ImplementsCycleContract cycleContract Naming.ports :=
  Internal.construction_correct

theorem implements_contract :
    Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds := certification.implements

theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨certified.certification.structural.hasSolution, certified.certification.structural.hasAtMostOneSolution⟩


end PicoRV.Control.ControlNext
