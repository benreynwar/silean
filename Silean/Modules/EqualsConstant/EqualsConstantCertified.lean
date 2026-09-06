import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Modules.EqualsConstant.EqualsConstant

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

private theorem implements : Contracts.Cycle.Implements
    (certificationStructure signalType constant layerChildren)
    (cycleContract signalType constant)
    (stateCorresponds signalType constant layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, proposals⟩
  have childMatch (child : Instance) := by
    letI : Subsingleton ((childContracts signalType constant child).state.Values) := by
      cases child <;> change Subsingleton emptySignalMap.Values <;> infer_instance
    exact childSolutionMatchesContract_of_subsingletonState layerChildren inputs
      structuralState (ProposedValues.composite outputs proposals) satisfies child
      (by cases child <;> exact SignalMap.emptyValues)
  have constantOutput : (proposals .constantValue).outputs .output = constant :=
    (Constant.outputRule_holds_iff signalType constant _ _ _).mp
      ((childMatch .constantValue).1.1 Primitives.ConstantRule.apply)
  have equalityOutput : (proposals .equality).outputs .result =
      signalType.equal (inputs .value) ((proposals .constantValue).outputs .output) := by
    have held := (Equality.outputRule_holds_iff signalType _ _ _).mp
      ((childMatch .equality).1.1 Equality.Rule.apply)
    have inputsEqual : ProposedValues.childInputs (body signalType constant)
        (fun name => (layerChildren name).moduleStructure) inputs proposals .equality =
          (fun | .left => inputs .value
               | .right => (proposals .constantValue).outputs .output) := by
      funext input
      cases input <;> rfl
    change (proposals .equality).outputs .result = signalType.equal
      ((ProposedValues.childInputs (body signalType constant) _ inputs proposals
        .equality) .left)
      ((ProposedValues.childInputs (body signalType constant) _ inputs proposals
        .equality) .right) at held
    rw [inputsEqual] at held
    exact held
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    change outputs .result = signalType.equal (inputs .value) constant
    rw [show outputs .result = (proposals .equality).outputs .result by
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
