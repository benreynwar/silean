import PicoRV.Decoder.Internal.DecoderInstructionSummaryVerification

/-! Public instruction-summary declarations backed by generated internals. -/

namespace PicoRV.Decoder.InstructionSummary

open Silean
open Silean.Authoring.CircuitDescription

noncomputable def place
    (inputs : (input : ports.inputs.Label) → Net (ports.inputs.signalType input)) :
    Builder ((output : ports.outputs.Label) →
      Net (ports.outputs.signalType output)) :=
  placeIndexed "decoder_instruction_summary" Structure.design inputs

attribute [circuit_description] place

/-- Every realized step has the public summary behavior. -/
theorem outputs_of_realization {step : Structure.moduleStructure.Step}
    (realizes : Structure.moduleStructure.Realizes step) :
    step.outputs = outputValues (valuesOf step.inputs) := by
  rcases Structure.certified.hasCorrespondingState step.currentState with
    ⟨contractState, corresponds⟩
  rcases Structure.certified.implements contractState step corresponds realizes with
    ⟨_, allowed, _⟩
  exact outputs_of_allowed allowed

theorem implements_contract :
    Contracts.Cycle.Implements Structure.moduleStructure cycleContract
      Structure.certification.stateCorresponds :=
  Structure.certification.implements

theorem hasExactlyOneSolution : Structure.moduleStructure.HasExactlyOneSolution :=
  ⟨Structure.certified.certification.structural.hasSolution,
    Structure.certified.certification.structural.hasAtMostOneSolution⟩


end PicoRV.Decoder.InstructionSummary
