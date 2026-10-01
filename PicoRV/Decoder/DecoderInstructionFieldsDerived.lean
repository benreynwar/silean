import PicoRV.Decoder.Internal.DecoderInstructionFieldsVerification

/-! Public instruction-field declarations backed by generated internals. -/

namespace PicoRV.Decoder.InstructionFields

open Silean
open Silean.Authoring.CircuitDescription

/-- Place the shared instruction-field decoder. -/
noncomputable def place (word : Net (.vector 32 .bit)) :
    Builder ports.OutputNets :=
  ports.placeIndexed "decoder_instruction_fields" Structure.moduleStructure
    Structure.naming word

attribute [circuit_description] place

/-- Every realized step exposes the predicates decoded from `word`. -/
theorem outputs_of_realization {step : Structure.moduleStructure.Step}
    (realizes : Structure.moduleStructure.Realizes step) :
    step.outputs = outputValues (step.inputs .word) := by
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


end PicoRV.Decoder.InstructionFields
