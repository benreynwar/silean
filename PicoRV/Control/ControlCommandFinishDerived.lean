import PicoRV.Control.Internal.ControlCommandFinishVerification

/-! Public command-finishing declarations backed by generated internals. -/

namespace PicoRV.Control.CommandFinish

open Silean
open Silean.Authoring.CircuitDescription

noncomputable def placeNamed (name : Naming.SourceName)
    (clear : Net .bit) (transition : Net transitionType) :
    Builder (Net stateType) := do
  let child ← Authoring.CircuitDescription.placeNamed name design fun
    | .clear => clear
    | .transition => transition
  pure (child .state)

noncomputable def place (clear : Net .bit) (transition : Net transitionType) :
    Builder (Net stateType) := do
  let child ← placeIndexed "command_finish" design fun
    | .clear => clear
    | .transition => transition
  pure (child .state)

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


end PicoRV.Control.CommandFinish
