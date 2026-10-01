import PicoRV.Decoder.Internal.DecoderInstructionMatchGateVerification

/-! Public match-gate declarations backed by generated internals. -/

namespace PicoRV.Decoder.InstructionMatch.MatchGate

open Silean
open Silean.Authoring.CircuitDescription

noncomputable def place (broad field qualifier : Net .bit) :
    Builder (Net .bit) := do
  let outputs ← ports.placeIndexed "instruction_match_gate"
    Structure.moduleStructure Structure.naming broad field qualifier
  pure outputs.result

noncomputable def placeNamed (name : Naming.SourceName)
    (broad field qualifier : Net .bit) : Builder (Net .bit) := do
  let outputs ← ports.placeNamed name
    Structure.moduleStructure Structure.naming broad field qualifier
  pure outputs.result

attribute [circuit_description] place placeNamed

/-- The authored match gate implements its exact cycle contract. -/
theorem construction_correct :
    description.ImplementsCycleContract cycleContract Naming.ports :=
  Internal.construction_correct

/-- Every realized step returns the conjunction of all conditions. -/
theorem result_of_realization {step : Structure.moduleStructure.Step}
    (realizes : Structure.moduleStructure.Realizes step) :
    step.outputs .result =
      ((step.inputs .broad && step.inputs .field) && step.inputs .qualifier) := by
  rcases Structure.certified.hasCorrespondingState step.currentState with
    ⟨contractState, corresponds⟩
  rcases Structure.certified.implements contractState step corresponds realizes with
    ⟨_, allowed, _⟩
  exact result_of_allowed allowed

theorem implements_contract :
    Contracts.Cycle.Implements Structure.moduleStructure cycleContract
      Structure.certification.stateCorresponds :=
  Structure.certification.implements

theorem hasExactlyOneSolution : Structure.moduleStructure.HasExactlyOneSolution :=
  ⟨Structure.certified.certification.structural.hasSolution,
    Structure.certified.certification.structural.hasAtMostOneSolution⟩


end PicoRV.Decoder.InstructionMatch.MatchGate
