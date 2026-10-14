import Silean.Authoring.CircuitDescriptionContracts
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Modules.SignedMultiply.Internal.SignedMultiplyArithmetic

/-! Internal schedules, structural certification, and authored-description
correspondence for `SignedMultiply`. -/

namespace Silean.Modules.SignedMultiply

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (leftWidth : Nat) (rightWidth : Nat)
    for body leftWidth rightWidth where
  leftSignLayout := VectorLayout.certification leftWidth 1 (signLayout leftWidth),
  leftSignSplit :=
    ((Composition.SignalSplitter.vector 1 .bit).certified).certification,
  rightSignLayout := VectorLayout.certification rightWidth 1 (signLayout rightWidth),
  rightSignSplit :=
    ((Composition.SignalSplitter.vector 1 .bit).certified).certification,
  leftMagnitude := ConditionalNegate.certification leftWidth,
  rightMagnitude := ConditionalNegate.certification rightWidth,
  productSign := Primitives.xorCertified.certification,
  magnitudeProduct := UnsignedMultiply.certification leftWidth rightWidth,
  resultNegate := ConditionalNegate.certification (leftWidth + rightWidth)

module_rule_schedules derivedRuleSchedules (leftWidth : Nat) (rightWidth : Nat)
    for body leftWidth rightWidth with childContracts leftWidth rightWidth
    implementing cycleContract leftWidth rightWidth where
  output | .apply =>
    [.leftSignLayout => VectorLayout.Rule.apply,
      .leftSignSplit => Composition.SignalComponentRule.apply,
      .rightSignLayout => VectorLayout.Rule.apply,
      .rightSignSplit => Composition.SignalComponentRule.apply,
      .leftMagnitude => ConditionalNegate.Rule.apply,
      .rightMagnitude => ConditionalNegate.Rule.apply,
      .productSign => Primitives.XorRule.apply,
      .magnitudeProduct => UnsignedMultiply.Rule.apply,
      .resultNegate => ConditionalNegate.Rule.apply]
  state := []

section LayerCertification

variable (leftWidth rightWidth : Nat)
  (layerChildren : ChildStructures (body leftWidth rightWidth)
    (childContracts leftWidth rightWidth))

private theorem implements :
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body leftWidth rightWidth) layerChildren)
      (cycleContract leftWidth rightWidth) (fun _ _ => True) := by
  intro contractState hierStep corresponds satisfies
  have boundary := satisfies.1

  derive_empty_state_child_matches childMatch for body leftWidth rightWidth from
    layerChildren, hierStep, satisfies

  have leftLayout := (childMatch .leftSignLayout).boundaryOutput
    (VectorLayout.cycleContract.outputEquation leftWidth 1
      (signLayout leftWidth))
  change hierStep.childOutputs .leftSignLayout .output =
    VectorLayout.apply (signLayout leftWidth) (hierStep.inputs .left) at leftLayout
  have rightLayout := (childMatch .rightSignLayout).boundaryOutput
    (VectorLayout.cycleContract.outputEquation rightWidth 1
      (signLayout rightWidth))
  change hierStep.childOutputs .rightSignLayout .output =
    VectorLayout.apply (signLayout rightWidth) (hierStep.inputs .right) at rightLayout

  have leftSplit :=
    (Composition.SignalSplitter.outputRule_holds_iff
      (.vector 1 .bit) _ SignalMap.emptyValues _).mp
      ((childMatch .leftSignSplit).ruleHolds
        Composition.SignalComponentRule.apply)
  have rightSplit :=
    (Composition.SignalSplitter.outputRule_holds_iff
      (.vector 1 .bit) _ SignalMap.emptyValues _).mp
      ((childMatch .rightSignSplit).ruleHolds
        Composition.SignalComponentRule.apply)

  have leftSign : hierStep.childOutputs .leftSignSplit 0 =
      (BitVector.toBitVec leftWidth (hierStep.inputs .left)).msb := by
    have equation := congrFun leftSplit 0
    change hierStep.childOutputs .leftSignSplit 0 =
      hierStep.childOutputs .leftSignLayout .output 0 at equation
    rw [equation, leftLayout]
    exact Internal.signLayout_apply leftWidth (hierStep.inputs .left)
  have rightSign : hierStep.childOutputs .rightSignSplit 0 =
      (BitVector.toBitVec rightWidth (hierStep.inputs .right)).msb := by
    have equation := congrFun rightSplit 0
    change hierStep.childOutputs .rightSignSplit 0 =
      hierStep.childOutputs .rightSignLayout .output 0 at equation
    rw [equation, rightLayout]
    exact Internal.signLayout_apply rightWidth (hierStep.inputs .right)

  have leftMagnitude := (childMatch .leftMagnitude).boundaryFact
    (property := fun inputs outputs =>
      BitVector.toBitVec leftWidth (outputs .result) =
        bif inputs .negate then -BitVector.toBitVec leftWidth (inputs .value)
        else BitVector.toBitVec leftWidth (inputs .value))
    (fun {step} allowed =>
      ConditionalNegate.result_toBitVec_of_allowed leftWidth
        (step := step) allowed)
  change BitVector.toBitVec leftWidth
      (hierStep.childOutputs .leftMagnitude .result) =
    bif hierStep.childOutputs .leftSignSplit 0 then
      -BitVector.toBitVec leftWidth (hierStep.inputs .left)
    else
      BitVector.toBitVec leftWidth (hierStep.inputs .left) at leftMagnitude
  have rightMagnitude := (childMatch .rightMagnitude).boundaryFact
    (property := fun inputs outputs =>
      BitVector.toBitVec rightWidth (outputs .result) =
        bif inputs .negate then -BitVector.toBitVec rightWidth (inputs .value)
        else BitVector.toBitVec rightWidth (inputs .value))
    (fun {step} allowed =>
      ConditionalNegate.result_toBitVec_of_allowed rightWidth
        (step := step) allowed)
  change BitVector.toBitVec rightWidth
      (hierStep.childOutputs .rightMagnitude .result) =
    bif hierStep.childOutputs .rightSignSplit 0 then
      -BitVector.toBitVec rightWidth (hierStep.inputs .right)
    else
      BitVector.toBitVec rightWidth (hierStep.inputs .right) at rightMagnitude
  rw [leftSign] at leftMagnitude
  rw [rightSign] at rightMagnitude
  have leftMagnitudeAbs : BitVector.toBitVec leftWidth
      (hierStep.childOutputs .leftMagnitude .result) =
    (BitVector.toBitVec leftWidth (hierStep.inputs .left)).abs := by
    rw [leftMagnitude]
    cases sign : (BitVector.toBitVec leftWidth (hierStep.inputs .left)).msb <;>
      simp [BitVec.abs_eq, sign]
  have rightMagnitudeAbs : BitVector.toBitVec rightWidth
      (hierStep.childOutputs .rightMagnitude .result) =
    (BitVector.toBitVec rightWidth (hierStep.inputs .right)).abs := by
    rw [rightMagnitude]
    cases sign : (BitVector.toBitVec rightWidth (hierStep.inputs .right)).msb <;>
      simp [BitVec.abs_eq, sign]

  have productSign := (Primitives.xorOutputRule_holds_iff _ _ _).mp
    ((childMatch .productSign).ruleHolds Primitives.XorRule.apply)
  change hierStep.childOutputs .productSign .output =
    Primitives.xorValue
      (hierStep.childOutputs .leftSignSplit 0)
      (hierStep.childOutputs .rightSignSplit 0) at productSign
  rw [leftSign, rightSign] at productSign

  have magnitudeProduct := (childMatch .magnitudeProduct).boundaryOutput
    (UnsignedMultiply.cycleContract.resultEquation leftWidth rightWidth)
  change hierStep.childOutputs .magnitudeProduct .result =
    UnsignedMultiply.resultValue leftWidth rightWidth
      (hierStep.childOutputs .leftMagnitude .result)
      (hierStep.childOutputs .rightMagnitude .result) at magnitudeProduct
  have magnitudeProductNative := congrArg
    (BitVector.toBitVec (leftWidth + rightWidth)) magnitudeProduct
  simp only [UnsignedMultiply.resultValue,
    BitVector.toBitVec_ofNat] at magnitudeProductNative
  rw [← BitVector.toBitVec_toNat leftWidth,
    ← BitVector.toBitVec_toNat rightWidth,
    leftMagnitudeAbs, rightMagnitudeAbs] at magnitudeProductNative

  have resultNegate := (childMatch .resultNegate).boundaryFact
    (property := fun inputs outputs =>
      BitVector.toBitVec (leftWidth + rightWidth) (outputs .result) =
        bif inputs .negate then
          -BitVector.toBitVec (leftWidth + rightWidth) (inputs .value)
        else
          BitVector.toBitVec (leftWidth + rightWidth) (inputs .value))
    (fun {step} allowed =>
      ConditionalNegate.result_toBitVec_of_allowed
        (leftWidth + rightWidth) (step := step) allowed)
  change BitVector.toBitVec (leftWidth + rightWidth)
      (hierStep.childOutputs .resultNegate .result) =
    bif hierStep.childOutputs .productSign .output then
      -BitVector.toBitVec (leftWidth + rightWidth)
        (hierStep.childOutputs .magnitudeProduct .result)
    else
      BitVector.toBitVec (leftWidth + rightWidth)
        (hierStep.childOutputs .magnitudeProduct .result) at resultNegate
  rw [productSign, magnitudeProductNative] at resultNegate
  rw [Internal.signed_product_algorithm] at resultNegate

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [applyRule_holds_iff]
    dsimp only
    change @Eq (Fin (leftWidth + rightWidth) → Bool)
      (hierStep.outputs .result)
      (resultValue leftWidth rightWidth
        (hierStep.inputs .left) (hierStep.inputs .right))
    have parentNative : BitVector.toBitVec (leftWidth + rightWidth)
        (hierStep.outputs .result) =
      BitVec.ofInt (leftWidth + rightWidth)
        ((BitVector.toBitVec leftWidth (hierStep.inputs .left)).toInt *
          (BitVector.toBitVec rightWidth (hierStep.inputs .right)).toInt) := by
      rw [show hierStep.outputs .result =
          hierStep.childOutputs .resultNegate .result by exact boundary .result]
      exact resultNegate
    have vectors := congrArg BitVector.ofBitVec parentNative
    simpa [resultValue] using vectors
  · funext label
    exact nomatch label

end LayerCertification

module_cycle_certification certification (leftWidth : Nat) (rightWidth : Nat)
    for moduleStructure leftWidth rightWidth via body leftWidth rightWidth
    with childContracts leftWidth rightWidth
    implementing cycleContract leftWidth rightWidth where
  schedules := derivedRuleSchedules leftWidth rightWidth,
  structuralChildren := structuralChildren leftWidth rightWidth,
  certifiedChildren := certifiedChildren leftWidth rightWidth,
  structuresMatch := certifiedChildren_moduleStructure leftWidth rightWidth,
  stateCorresponds := fun _ _ _ => True,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements leftWidth rightWidth

end Silean.Modules.SignedMultiply

/-! ## Authored-description correspondence -/

namespace Silean.Modules.SignedMultiply.Internal

open Silean Naming Authoring.CircuitDescription

private theorem same (leftWidth rightWidth : Nat) :
    some (description leftWidth rightWidth) =
      ofNaming (SignedMultiply.naming leftWidth rightWidth) := by
  simp [circuit_description, description, construction,
    VectorLayout.place, ConditionalNegate.place, UnsignedMultiply.place,
    enumeration]
  rfl

theorem description_corresponds (leftWidth rightWidth : Nat) :
    Corresponds (description leftWidth rightWidth)
      (SignedMultiply.naming leftWidth rightWidth) :=
  ⟨same leftWidth rightWidth⟩

open Authoring.CircuitDescription.Description

/-- The authored signed-multiplier construction implements its cycle
contract. -/
theorem construction_correct (leftWidth rightWidth : Nat) :
    ImplementsCycleContract (description leftWidth rightWidth)
      (cycleContract leftWidth rightWidth)
      (Naming.ports leftWidth rightWidth) := by
  have corresponds := description_corresponds leftWidth rightWidth
  unfold SignedMultiply.naming at corresponds
  simp only [id_eq] at corresponds
  exact ImplementsCycleContract.of_certification
    (referenceBody := {
      instancePorts := instancePorts leftWidth rightWidth,
      wiring := wiring leftWidth rightWidth })
    (children := structuralChildren leftWidth rightWidth)
    corresponds (certification leftWidth rightWidth)

end Silean.Modules.SignedMultiply.Internal
