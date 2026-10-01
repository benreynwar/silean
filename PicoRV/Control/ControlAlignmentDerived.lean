import PicoRV.Control.Internal.ControlAlignmentVerification

/-! Public alignment declarations backed by generated internals. -/

namespace PicoRV.Control.Alignment

open Silean
open Silean.Authoring.CircuitDescription

structure PlacedOutputs where
  data : Net .bit
  instruction : Net .bit

noncomputable def placeNamed (name : Naming.SourceName)
    (inputs : Net inputsType) (current : Net stateType) :
    Builder PlacedOutputs := do
  let child ← Authoring.CircuitDescription.placeNamed name design fun
    | .inputs => inputs
    | .current => current
  pure { data := child .data, instruction := child .instruction }

noncomputable def place (inputs : Net inputsType) (current : Net stateType) :
    Builder PlacedOutputs := do
  let child ← placeIndexed "alignment" design fun
    | .inputs => inputs
    | .current => current
  pure { data := child .data, instruction := child .instruction }

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


end PicoRV.Control.Alignment
