import Silean.Modules.BitMux.Internal.BitMuxVerification

/-! Public bit-mux declarations backed by generated internals. -/

namespace Silean.Modules.BitMux

open Silean
open Authoring.CircuitDescription

/-- Place a bit mux under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Naming.SourceName)
    (select whenFalse whenTrue : Net .bit) : Builder (Net .bit) := do
  let outputs ← ports.placeNamed name moduleStructure naming
    select whenFalse whenTrue
  pure outputs.result

/-- Place a bit mux using the next conventional indexed name. -/
noncomputable def place (select whenFalse whenTrue : Net .bit) :
    Builder (Net .bit) := do
  let outputs ← ports.placeIndexed "bit_mux" moduleStructure naming
    select whenFalse whenTrue
  pure outputs.result

attribute [circuit_description] placeNamed place

/-- The authored bit mux implements its exact selection contract. -/
theorem construction_correct :
    description.ImplementsCycleContract cycleContract Naming.ports :=
  Internal.construction_correct

/-- Every realizable bit-mux step selects the requested input. -/
theorem result_of_realization {step : moduleStructure.Step}
    (realizes : moduleStructure.Realizes step) :
    step.outputs .result =
      bif step.inputs .select then step.inputs .whenTrue else step.inputs .whenFalse := by
  obtain ⟨contractState, corresponds⟩ :=
    certification.hasCorrespondingState step.currentState
  obtain ⟨_, allowed, _⟩ :=
    certification.allows_of_realizes contractState step corresponds realizes
  exact cycleContract.result allowed

/-- The generated hierarchy implements the exact bit-mux contract. -/
theorem implements_contract :
    Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

end Silean.Modules.BitMux
