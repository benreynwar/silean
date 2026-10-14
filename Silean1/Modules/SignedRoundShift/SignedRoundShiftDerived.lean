import Silean.Modules.SignedRoundShift.Internal.SignedRoundShiftVerification

/-! Public placement and correctness declarations for the structural signed
rounded-shift circuit. -/

namespace Silean.Modules.SignedRoundShift

open Silean
open Authoring.CircuitDescription

noncomputable def placeNamed (name : Naming.SourceName)
    (value : Net (.vector (discardedWidth + retainedWidth) .bit)) :
    Builder (Net (.vector retainedWidth .bit)) := do
  let outputs ← ports.placeNamed retainedWidth discardedWidth name
    (moduleStructure retainedWidth discardedWidth)
    (naming retainedWidth discardedWidth) value
  pure outputs.result

noncomputable def place
    (value : Net (.vector (discardedWidth + retainedWidth) .bit)) :
    Builder (Net (.vector retainedWidth .bit)) := do
  let outputs ← ports.placeIndexed retainedWidth discardedWidth
    "signed_round_shift" (moduleStructure retainedWidth discardedWidth)
    (naming retainedWidth discardedWidth) value
  pure outputs.result

attribute [circuit_description] placeNamed place

theorem result_of_realization (retainedWidth discardedWidth : Nat)
    {step : (moduleStructure retainedWidth discardedWidth).Step}
    (realizes :
      (moduleStructure retainedWidth discardedWidth).Realizes step) :
    step.outputs .result =
      resultValue retainedWidth discardedWidth (step.inputs .value) := by
  obtain ⟨contractState, corresponds⟩ :=
    (certification retainedWidth discardedWidth).hasCorrespondingState
      step.currentState
  obtain ⟨_, allowed, _⟩ :=
    (certification retainedWidth discardedWidth).allows_of_realizes
      contractState step corresponds realizes
  exact cycleContract.result retainedWidth discardedWidth allowed

theorem implements_contract (retainedWidth discardedWidth : Nat) :
    Contracts.Cycle.Implements
      (moduleStructure retainedWidth discardedWidth)
      (cycleContract retainedWidth discardedWidth)
      (certification retainedWidth discardedWidth).stateCorresponds :=
  (certification retainedWidth discardedWidth).implements

end Silean.Modules.SignedRoundShift
