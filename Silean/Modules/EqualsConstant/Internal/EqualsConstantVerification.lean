import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Authoring.CircuitDescriptionSoundness
import Silean.Modules.EqualsConstant.EqualsConstant
import Silean.Modules.Equality.EqualityTheorems

/-! # EqualsConstant verification

Child certifications, schedules, and the structural proof for the circuit in
\`EqualsConstant.lean\`. Import \`EqualsConstantTheorems.lean\` for the public
proof interface. -/

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
    (Constant.outputRule_holds_iff signalType constant _ _ _).mp
      ((childMatch .constantValue).ruleHolds Primitives.ConstantRule.apply)
  have equalityOutput : (hierStep.children .equality).outputs .result =
      signalType.equal (hierStep.inputs .value)
        ((hierStep.children .constantValue).outputs .output) := by
    have held := (Equality.outputRule_holds_iff signalType _ _ _).mp
      ((childMatch .equality).ruleHolds Equality.Rule.apply)
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
    rw [outputRule_holds_iff]
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

namespace Silean.Modules.EqualsConstant.Description.Internal

open Silean Naming Authoring.CircuitDescription

private theorem same (signalType : SignalType)
    (constant : signalType.Denote) :
    some (description signalType constant) =
      ofNaming (EqualsConstant.naming signalType constant) := by
  rfl

private theorem unique (signalType : SignalType)
    (constant : signalType.Denote) :
    (description signalType constant).UniqueNames := by
  refine ⟨of_decide_eq_true rfl, of_decide_eq_true rfl, ?_⟩
  intro child member
  change child ∈ [_, _] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal <;> subst child <;>
    constructor <;> simp only [Equality.Naming.naming_ports] <;>
    exact of_decide_eq_true rfl

theorem corresponds (signalType : SignalType)
    (constant : signalType.Denote) :
    Corresponds (description signalType constant)
      (EqualsConstant.naming signalType constant) :=
  ⟨same signalType constant, unique signalType constant⟩

end Silean.Modules.EqualsConstant.Description.Internal
