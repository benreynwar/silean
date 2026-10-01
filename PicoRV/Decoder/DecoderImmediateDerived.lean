import PicoRV.Decoder.Internal.DecoderImmediateVerification

/-! Public immediate-decoder declarations backed by generated internals. -/

namespace PicoRV.Decoder.Immediate

open Silean
open Silean.Authoring.CircuitDescription
open PicoRV.Decoder

noncomputable def place
    (inputs : (input : ports.inputs.Label) → Net (ports.inputs.signalType input)) :
    Builder ((output : ports.outputs.Label) →
      Net (ports.outputs.signalType output)) :=
  placeIndexed "decoder_immediate" design inputs

noncomputable def placeNamed (name : Naming.SourceName)
    (inputs : (input : ports.inputs.Label) → Net (ports.inputs.signalType input)) :
    Builder ((output : ports.outputs.Label) →
      Net (ports.outputs.signalType output)) :=
  Authoring.CircuitDescription.placeNamed name design inputs

attribute [circuit_description] place placeNamed

theorem immediateI_layout (word : Word) :
    Silean.Modules.VectorLayout.apply immediateILayout word = immediateI word :=
  Internal.immediateI_layout word

theorem immediateU_layout (word : Word) :
    Silean.Modules.VectorLayout.apply immediateULayout word = immediateU word :=
  Internal.immediateU_layout word

theorem immediateS_layout (word : Word) :
    Silean.Modules.VectorLayout.apply immediateSLayout word = immediateS word :=
  Internal.immediateS_layout word

theorem immediateB_layout (word : Word) :
    Silean.Modules.VectorLayout.apply immediateBLayout word = immediateB word :=
  Internal.immediateB_layout word

theorem construction_correct :
    description.ImplementsCycleContract cycleContract Naming.ports :=
  Internal.construction_correct

theorem outputs_of_realization {step : moduleStructure.Step}
    (realizes : moduleStructure.Realizes step) :
    step.outputs = outputValues (valuesOf step.inputs) := by
  rcases certified.hasCorrespondingState step.currentState with
    ⟨contractState, corresponds⟩
  rcases certified.implements contractState step corresponds realizes with
    ⟨_, allowed, _⟩
  exact outputs_of_allowed allowed

theorem implements_contract :
    Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨certified.certification.structural.hasSolution, certified.certification.structural.hasAtMostOneSolution⟩


end PicoRV.Decoder.Immediate
