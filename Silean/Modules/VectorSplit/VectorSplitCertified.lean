import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.VectorSplit.VectorSplit

namespace Silean.Modules.VectorSplit

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (element : SignalType)
    (leftWidth : Nat) (rightWidth : Nat) for body element leftWidth rightWidth where
  split := (splitter element leftWidth rightWidth).certified.certification,
  left := (leftCombiner element leftWidth).certified.certification,
  right := (rightCombiner element rightWidth).certified.certification

module_rule_schedules derivedRuleSchedules (element : SignalType)
    (leftWidth : Nat) (rightWidth : Nat) for body element leftWidth rightWidth
    with childContracts element leftWidth rightWidth
    implementing cycleContract element leftWidth rightWidth where
  output | .apply => [
    .split => Composition.SignalComponentRule.apply,
    .left => Composition.SignalComponentRule.apply,
    .right => Composition.SignalComponentRule.apply]
  state := []

def splitInputs (element : SignalType) (leftWidth rightWidth : Nat)
    (inputs : (ports element leftWidth rightWidth).inputs.Values) :
    (splitter element leftWidth rightWidth).ports.inputs.Values
  | .value => inputs .value

section LayerCertification

variable (element : SignalType) (leftWidth rightWidth : Nat)
  (layerChildren : (child : Instance) →
    Contracts.Cycle.ModuleCycleCertifiedStructure
      (childContracts element leftWidth rightWidth child))

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure
    (body element leftWidth rightWidth) layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure element leftWidth rightWidth layerChildren).State) : Prop := True

private theorem implements : Contracts.Cycle.Implements
    (certificationStructure element leftWidth rightWidth layerChildren)
    (cycleContract element leftWidth rightWidth)
    (stateCorresponds element leftWidth rightWidth layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, proposals⟩
  have boundary := satisfies.1
  have childMatch (child : Instance) := by
    letI : Subsingleton
        ((childContracts element leftWidth rightWidth child).state.Values) := by
      cases child <;> change Subsingleton emptySignalMap.Values <;> infer_instance
    exact childSolutionMatchesContract_of_subsingletonState layerChildren inputs
      structuralState (ProposedValues.composite outputs proposals) satisfies child
      (by cases child <;> exact SignalMap.emptyValues)
  have splitOutputs : (proposals .split).outputs =
      (splitter element leftWidth rightWidth).outputValues
        (splitInputs element leftWidth rightWidth inputs) := by
    have holds := (Composition.SignalSplitter.outputRule_holds_iff
      (splitter element leftWidth rightWidth) _ _ _).mp
      ((childMatch .split).1.1 Composition.SignalComponentRule.apply)
    have inputsEqual : ProposedValues.childInputs (body element leftWidth rightWidth) _
        inputs proposals .split = splitInputs element leftWidth rightWidth inputs := by
      funext input; cases input; rfl
    change (proposals .split).outputs =
      (splitter element leftWidth rightWidth).outputValues
        (ProposedValues.childInputs (body element leftWidth rightWidth) _
          inputs proposals .split) at holds
    rw [inputsEqual] at holds
    exact holds
  have leftOutputs : (proposals .left).outputs =
      (leftCombiner element leftWidth).outputValues
        (ProposedValues.childInputs (body element leftWidth rightWidth) _
          inputs proposals .left) :=
    (Composition.SignalCombiner.outputRule_holds_iff _ _ _ _).mp
      ((childMatch .left).1.1 Composition.SignalComponentRule.apply)
  have rightOutputs : (proposals .right).outputs =
      (rightCombiner element rightWidth).outputValues
        (ProposedValues.childInputs (body element leftWidth rightWidth) _
          inputs proposals .right) :=
    (Composition.SignalCombiner.outputRule_holds_iff _ _ _ _).mp
      ((childMatch .right).1.1 Composition.SignalComponentRule.apply)
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    constructor
    · change outputs .left = leftPart (inputs .value)
      rw [show outputs .left = (proposals .left).outputs .value by
        exact boundary .left]
      rw [congrFun leftOutputs .value]
      funext index
      change (proposals .split).outputs (Fin.castAdd rightWidth index) =
        inputs .value (Fin.castAdd rightWidth index)
      rw [splitOutputs]
      rfl
    · change outputs .right = rightPart (inputs .value)
      rw [show outputs .right = (proposals .right).outputs .value by
        exact boundary .right]
      rw [congrFun rightOutputs .value]
      funext index
      change (proposals .split).outputs (Fin.natAdd leftWidth index) =
        inputs .value (Fin.natAdd leftWidth index)
      rw [splitOutputs]
      rfl
  · rfl

end LayerCertification

module_cycle_certification certification (element : SignalType)
    (leftWidth : Nat) (rightWidth : Nat)
    for moduleStructure element leftWidth rightWidth
    via body element leftWidth rightWidth
    with childContracts element leftWidth rightWidth
    implementing cycleContract element leftWidth rightWidth where
  schedules := derivedRuleSchedules element leftWidth rightWidth,
  structuralChildren := structuralChildren element leftWidth rightWidth,
  certifiedChildren := certifiedChildren element leftWidth rightWidth,
  structuresMatch := certifiedChildren_moduleStructure element leftWidth rightWidth,
  stateCorresponds := stateCorresponds element leftWidth rightWidth,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements element leftWidth rightWidth

end Silean.Modules.VectorSplit
