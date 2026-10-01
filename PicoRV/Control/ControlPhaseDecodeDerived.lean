import PicoRV.Control.Internal.ControlPhaseDecodeVerification

/-! Public phase-decoder declarations backed by generated internals. -/

namespace PicoRV.Control.PhaseDecode

open Silean
open Silean.Authoring.CircuitDescription

structure PlacedOutputs where
  trap : Net .bit
  fetch : Net .bit
  loadRs1 : Net .bit
  loadRs2 : Net .bit
  execute : Net .bit
  shift : Net .bit
  store : Net .bit
  load : Net .bit

noncomputable def placeNamed (name : Naming.SourceName)
    (state : Net (.vector 8 .bit)) : Builder PlacedOutputs := do
  let child ← Authoring.CircuitDescription.placeNamed name design fun
    | .cpu_state => state
  pure {
    trap := child .trap, fetch := child .fetch,
    loadRs1 := child .loadRs1, loadRs2 := child .loadRs2,
    execute := child .execute, shift := child .shift,
    store := child .store, load := child .load }

noncomputable def place (state : Net (.vector 8 .bit)) :
    Builder PlacedOutputs := do
  let child ← placeIndexed "control_phase_decode" design fun
    | .cpu_state => state
  pure {
    trap := child .trap, fetch := child .fetch,
    loadRs1 := child .loadRs1, loadRs2 := child .loadRs2,
    execute := child .execute, shift := child .shift,
    store := child .store, load := child .load }

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


end PicoRV.Control.PhaseDecode
