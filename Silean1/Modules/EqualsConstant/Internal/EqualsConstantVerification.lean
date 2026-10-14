import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Authoring.CircuitDescriptionSoundness
import Silean.Modules.EqualsConstant.Internal.EqualsConstantStructure
import Silean.Modules.Equality.EqualityDerived

/-! # EqualsConstant verification

Child certifications, schedules, correspondence, and structural correctness
for constant comparison. -/

namespace Silean.Modules.EqualsConstant

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (signalType : SignalType)
    (constant : signalType.Denote) for body signalType constant where
  constantValue := Constant.certification signalType constant,
  equality := Equality.certification signalType

module_rule_schedules derivedRuleSchedules (signalType : SignalType)
    (constant : signalType.Denote) for body signalType constant
    with childContracts signalType constant
    implementing cycleContract signalType constant where
  output | .apply => [
    .constantValue => Primitives.ConstantRule.apply,
    .equality => Equality.Rule.apply]
  state := []

section LayerCertification

variable (signalType : SignalType) (constant : signalType.Denote)
  (layerChildren : (child : (instancePorts signalType constant).Name) →
    Contracts.Cycle.ModuleCycleCertifiedStructure
      (childContracts signalType constant child))

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure
    (body signalType constant) layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure signalType constant layerChildren).State) : Prop := True

private theorem implements : Contracts.Cycle.ImplementsSolutions
    (certificationStructure signalType constant layerChildren)
    (cycleContract signalType constant)
    (stateCorresponds signalType constant layerChildren) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for body signalType constant from
    layerChildren, hierStep, satisfies
  have constantOutput :
      (hierStep.children .constantValue).outputs .output = constant :=
    Constant.output_of_allowed signalType constant
      (childMatch .constantValue).allowed
  have equalityOutput : (hierStep.children .equality).outputs .result =
      signalType.equal (hierStep.inputs .value)
        ((hierStep.children .constantValue).outputs .output) := by
    have held := Equality.cycleContract.result signalType
      (childMatch .equality).allowed
    have inputsEqual : (body signalType constant).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .equality =
          (fun | .left => hierStep.inputs .value
               | .right => (hierStep.children .constantValue).outputs .output) := by
      funext input
      cases input <;> rfl
    change (hierStep.children .equality).outputs .result = signalType.equal
      (((body signalType constant).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .equality) .left)
      (((body signalType constant).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .equality) .right) at held
    rw [inputsEqual] at held
    exact held
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [applyRule_holds_iff]
    change hierStep.outputs .result =
      signalType.equal (hierStep.inputs .value) constant
    rw [show hierStep.outputs .result =
        (hierStep.children .equality).outputs .result by
      exact satisfies.1 .result]
    rw [equalityOutput, constantOutput]
  · rfl

end LayerCertification

module_cycle_certification certification (signalType : SignalType)
    (constant : signalType.Denote) for moduleStructure signalType constant
    via body signalType constant with childContracts signalType constant
    implementing cycleContract signalType constant where
  schedules := derivedRuleSchedules signalType constant,
  structuralChildren := structuralChildren signalType constant,
  certifiedChildren := certifiedChildren signalType constant,
  structuresMatch := certifiedChildren_moduleStructure signalType constant,
  stateCorresponds := stateCorresponds signalType constant,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements signalType constant

end Silean.Modules.EqualsConstant

/-! ## Authored-description correspondence -/

namespace Silean.Modules.EqualsConstant.Internal

open Silean Naming Authoring.CircuitDescription

private theorem same (signalType : SignalType)
    (constant : signalType.Denote) :
    some (description signalType constant) =
      ofNaming (EqualsConstant.naming signalType constant) := by
  rfl

theorem description_corresponds (signalType : SignalType)
    (constant : signalType.Denote) :
    Corresponds (description signalType constant)
      (EqualsConstant.naming signalType constant) :=
  ⟨same signalType constant⟩

open Authoring.CircuitDescription.Description

/-- Generated proof behind the public implementation-independent correctness
claim. -/
theorem construction_correct (signalType : SignalType)
    (constant : signalType.Denote) :
    (description signalType constant).ImplementsCycleContract
      (cycleContract signalType constant) (Naming.ports signalType) := by
  have corresponds := description_corresponds signalType constant
  unfold EqualsConstant.naming at corresponds
  simp only [id_eq] at corresponds
  exact ImplementsCycleContract.of_certification
    (referenceBody := {
      instancePorts := instancePorts signalType constant
      wiring := wiring signalType constant })
    (children := structuralChildren signalType constant)
    corresponds (certification signalType constant)

end Silean.Modules.EqualsConstant.Internal
