import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.VectorReindex.Internal.VectorReindexStructure

namespace Silean.Modules.VectorReindex

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

open Internal

module_child_certifications childContracts (element : SignalType)
    (inputWidth : Nat) (outputWidth : Nat)
    (layout : Fin outputWidth → Fin inputWidth)
    for body element inputWidth outputWidth layout where
  split := (splitter element inputWidth).certified.certification,
  combine := (combiner element outputWidth).certified.certification

module_rule_schedules derivedRuleSchedules (element : SignalType)
    (inputWidth : Nat) (outputWidth : Nat)
    (layout : Fin outputWidth → Fin inputWidth)
    for body element inputWidth outputWidth layout
    with childContracts element inputWidth outputWidth layout
    implementing cycleContract element inputWidth outputWidth layout where
  output | .apply => [
    .split => Composition.SignalComponentRule.apply,
    .combine => Composition.SignalComponentRule.apply]
  state := []

section LayerCertification

variable (element : SignalType) (inputWidth outputWidth : Nat)
  (layout : Fin outputWidth → Fin inputWidth)
  (children : ChildStructures (body element inputWidth outputWidth layout)
    (childContracts element inputWidth outputWidth layout))

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure
    (body element inputWidth outputWidth layout) children

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure element inputWidth outputWidth layout children).State) :
    Prop := True

private theorem implements : Contracts.Cycle.ImplementsSolutions
    (certificationStructure element inputWidth outputWidth layout children)
    (cycleContract element inputWidth outputWidth layout)
    (stateCorresponds element inputWidth outputWidth layout children) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for
      body element inputWidth outputWidth layout from
    children, hierStep, satisfies
  have splitValue := ((splitter element inputWidth).outputRule_holds_iff _ _ _).mp
    ((childMatch .split).ruleHolds Composition.SignalComponentRule.apply)
  have combineValue := ((combiner element outputWidth).outputRule_holds_iff _ _ _).mp
    ((childMatch .combine).ruleHolds Composition.SignalComponentRule.apply)
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [applyRule_holds_iff]
    change hierStep.outputs .output =
      VectorReindex.apply layout (hierStep.inputs .input)
    rw [show hierStep.outputs .output =
        hierStep.childOutputs .combine .value by exact boundary .output]
    rw [combineValue]
    funext index
    simp only [Composition.SignalCombiner.outputValues, combiner,
      Wiring.childInputValues, wiring, EndpointContext.instanceOutput,
      SignalSource.value, VectorReindex.apply]
    have splitAt := congrFun splitValue (layout index)
    change hierStep.childOutputs .split (layout index) =
      hierStep.inputs .input (layout index) at splitAt
    exact splitAt
  · rfl

end LayerCertification

module_cycle_certification certification (element : SignalType)
    (inputWidth : Nat) (outputWidth : Nat)
    (layout : Fin outputWidth → Fin inputWidth)
    for moduleStructure element inputWidth outputWidth layout
    via body element inputWidth outputWidth layout
    with childContracts element inputWidth outputWidth layout
    implementing cycleContract element inputWidth outputWidth layout where
  schedules := derivedRuleSchedules element inputWidth outputWidth layout,
  structuralChildren := structuralChildren element inputWidth outputWidth layout,
  certifiedChildren := certifiedChildren element inputWidth outputWidth layout,
  structuresMatch :=
    certifiedChildren_moduleStructure element inputWidth outputWidth layout,
  stateCorresponds :=
    stateCorresponds element inputWidth outputWidth layout,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements element inputWidth outputWidth layout

end Silean.Modules.VectorReindex
