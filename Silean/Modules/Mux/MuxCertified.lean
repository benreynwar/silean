import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Mux.Mux
import Silean.Primitives.Not

namespace Silean.Modules.Mux

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (signalType : SignalType)
    for body signalType where
  invertSelect := Primitives.notCertified.certification,
  chooseFalse := Mask.certification signalType,
  chooseTrue := Mask.certification signalType,
  combine := BitwiseOr.certification signalType

module_rule_schedules derivedRuleSchedules (signalType : SignalType)
    for body signalType with childContracts signalType
    implementing cycleContract signalType where
  output
    | .select => [.invertSelect => Primitives.NotRule.apply,
      .chooseFalse => Mask.Rule.apply,
      .chooseTrue => Mask.Rule.apply,
      .combine => BitwiseOr.Rule.apply]
  state := []

mutual
  private theorem muxIdentity : ∀ (signalType : SignalType)
      (whenFalse whenTrue : signalType.Denote) (select : Bool),
      signalType.bitwiseOr
          (signalType.mask whenFalse (!select))
          (signalType.mask whenTrue select) =
        bif select then whenTrue else whenFalse
    | .bit, whenFalse, whenTrue, select => by
        cases select <;> cases whenFalse <;> cases whenTrue <;> rfl
    | .vector _ element, whenFalse, whenTrue, select => by
        cases select <;>
        funext index
        · exact muxIdentity element (whenFalse index) (whenTrue index) false
        · exact muxIdentity element (whenFalse index) (whenTrue index) true
    | .tuple fields, whenFalse, whenTrue, select =>
        muxFieldsIdentity fields whenFalse whenTrue select

  private theorem muxFieldsIdentity : ∀ (fields : SignalTypes)
      (whenFalse whenTrue : fields.Denote) (select : Bool),
      fields.bitwiseOr
          (fields.mask whenFalse (!select))
          (fields.mask whenTrue select) =
        bif select then whenTrue else whenFalse
    | .nil, (), (), _ => rfl
    | .cons head tail, (falseHead, falseTail), (trueHead, trueTail), select => by
        cases select
        · apply Prod.ext
          · exact muxIdentity head falseHead trueHead false
          · exact muxFieldsIdentity tail falseTail trueTail false
        apply Prod.ext
        · exact muxIdentity head falseHead trueHead true
        · exact muxFieldsIdentity tail falseTail trueTail true
end

section LayerCertification

variable (signalType : SignalType)
  (layerChildren : (child : (instancePorts signalType).Name) →
    Contracts.Cycle.ModuleCycleCertifiedStructure
      (childContracts signalType child))

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure (body signalType) layerChildren

private def stateCorresponds
    (_ : (cycleContract signalType).state.Values)
    (_ : (certificationStructure signalType layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.Implements (certificationStructure signalType layerChildren)
      (cycleContract signalType) (stateCorresponds signalType layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have childStateSubsingleton (child : Instance) :
      Subsingleton
        ((childContracts signalType child).state.Values) := by
    cases child <;> change Subsingleton emptySignalMap.Values <;> infer_instance
  have childMatch (child : Instance) := by
    letI := childStateSubsingleton child
    exact Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState
        proposal satisfies child (by cases child <;> exact SignalMap.emptyValues)
  have invertEvaluates := (childMatch .invertSelect).1
  have falseEvaluates := (childMatch .chooseFalse).1
  have trueEvaluates := (childMatch .chooseTrue).1
  have combineEvaluates := (childMatch .combine).1
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro name
    cases name
    change (selectRule signalType).Holds inputs contractState _
    rcases proposal with ⟨outputs, childProposals⟩
    have invertBit := (Primitives.notOutputRule_holds_iff _ _ _).mp
      (invertEvaluates.1 Primitives.NotRule.apply)
    have falseOutput := (Mask.outputRule_holds_iff signalType _ _ _).mp
      (falseEvaluates.1 Mask.Rule.apply)
    have trueOutput := (Mask.outputRule_holds_iff signalType _ _ _).mp
      (trueEvaluates.1 Mask.Rule.apply)
    have combineOutput := (BitwiseOr.outputRule_holds_iff signalType _ _ _).mp
      (combineEvaluates.1 BitwiseOr.Rule.apply)
    have boundaryResult := boundary .result
    change outputs .result = (childProposals .combine).outputs .result at boundaryResult
    change (childProposals .chooseFalse).outputs .result =
      signalType.mask (inputs .whenFalse)
        ((childProposals .invertSelect).outputs .output) at falseOutput
    change (childProposals .chooseTrue).outputs .result =
      signalType.mask (inputs .whenTrue) (inputs .select) at trueOutput
    change (childProposals .combine).outputs .result =
      signalType.bitwiseOr ((childProposals .chooseFalse).outputs .result)
        ((childProposals .chooseTrue).outputs .result) at combineOutput
    rw [selectRule_holds_iff signalType]
    change outputs .result =
      bif inputs .select then inputs .whenTrue else inputs .whenFalse
    rw [boundaryResult, combineOutput, falseOutput, trueOutput, invertBit]
    exact muxIdentity signalType _ _ _
  · simp [cycleContract, stateRule,
      Contracts.Cycle.CycleStateRule.apply]

end LayerCertification

module_cycle_certification certification (signalType : SignalType)
    for moduleStructure signalType via body signalType
    with childContracts signalType implementing cycleContract signalType where
  schedules := derivedRuleSchedules signalType,
  structuralChildren := structuralChildren signalType,
  certifiedChildren := certifiedChildren signalType,
  structuresMatch := certifiedChildren_moduleStructure signalType,
  stateCorresponds := stateCorresponds signalType,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements signalType

end Silean.Modules.Mux
