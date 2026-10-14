import Silean.Modules.UnsignedMultiply.Internal.UnsignedMultiplyVerification

/-! Public unsigned-multiplier declarations backed by the structural hierarchy. -/

namespace Silean.Modules.UnsignedMultiply

open Silean
open Authoring.CircuitDescription

/-- Place a full-width unsigned multiplier using the next conventional indexed
name. -/
noncomputable def place
    (left : Net (.vector leftWidth .bit))
    (right : Net (.vector rightWidth .bit)) :
    Builder (Net (.vector (leftWidth + rightWidth) .bit)) := do
  let outputs ← ports.placeIndexed leftWidth rightWidth "unsigned_multiply"
    (moduleStructure leftWidth rightWidth) (naming leftWidth rightWidth)
    left right
  pure outputs.result

attribute [circuit_description] place

/-- The hierarchy has exactly one structural solution for every boundary input
and physical state, independently of its behavioral contract. -/
theorem structuralCertification (leftWidth rightWidth : Nat) :
    ModuleStructuralCertification (moduleStructure leftWidth rightWidth) :=
  Internal.structuralCertification leftWidth rightWidth

/-- The structural multiplier implements exact full-width unsigned
multiplication. -/
theorem implements_contract (leftWidth rightWidth : Nat) :
    Contracts.Cycle.Implements
      (moduleStructure leftWidth rightWidth)
      (cycleContract leftWidth rightWidth)
      (certification leftWidth rightWidth).stateCorresponds :=
  (certification leftWidth rightWidth).implements

/-- Decoding the output of any structural realization gives the exact ordinary
natural-number product, with no truncation or wraparound. -/
theorem result_toNat_of_realization (leftWidth rightWidth : Nat)
    {step : (moduleStructure leftWidth rightWidth).Step}
    (realizes : (moduleStructure leftWidth rightWidth).Realizes step) :
    BitVector.toNat (leftWidth + rightWidth) (step.outputs .result) =
      BitVector.toNat leftWidth (step.inputs .left) *
        BitVector.toNat rightWidth (step.inputs .right) := by
  obtain ⟨_, _, allowed⟩ :=
    allowed_of_realization leftWidth rightWidth realizes
  exact result_toNat_of_allowed leftWidth rightWidth allowed

end Silean.Modules.UnsignedMultiply
