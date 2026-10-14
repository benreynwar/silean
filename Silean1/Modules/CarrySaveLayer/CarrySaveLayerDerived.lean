import Silean.Modules.CarrySaveLayer.Internal.CarrySaveLayerVerification

/-! Public carry-save-layer declarations backed by the indexed structure. -/

namespace Silean.Modules.CarrySaveLayer

open Silean
open Authoring.CircuitDescription

/-- Place one parallel carry-save compression layer. -/
noncomputable def place
    (operands : Net (.vector operandCount (.vector width .bit))) :
    Builder (Net (.vector (reducedCount operandCount) (.vector width .bit))) := do
  let outputs ← ports.placeIndexed width operandCount "carry_save_layer"
    (moduleStructure width operandCount) (naming width operandCount) operands
  pure outputs.reduced

attribute [circuit_description] place

/-- The generated hierarchy has exactly one structural solution for every
boundary input and physical state, independently of its behavioral contract. -/
theorem structuralCertification (width operandCount : Nat) :
    ModuleStructuralCertification (moduleStructure width operandCount) :=
  Internal.structuralCertification width operandCount

/-- Every realizable layer preserves the collection total and passes through
collections that contain no complete triple. -/
theorem contract_of_realization (width operandCount : Nat)
    {step : (moduleStructure width operandCount).Step}
    (realizes : (moduleStructure width operandCount).Realizes step) :
    contract width operandCount step.inputs step.outputs :=
  Internal.contract_of_realization width operandCount realizes

end Silean.Modules.CarrySaveLayer
