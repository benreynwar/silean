import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Modules.VectorLayout.VectorLayout
import Silean.Primitives.Constant

namespace Silean.Modules.VectorLayout

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (inputWidth : Nat) (outputWidth : Nat)
    (layout : Fin outputWidth → BitSource inputWidth)
    for body inputWidth outputWidth layout where
  split := (splitter inputWidth).certified.certification,
  falseBit := (Primitives.constantCertified false).certification,
  trueBit := (Primitives.constantCertified true).certification,
  combine := (combiner outputWidth).certified.certification

module_rule_schedules derivedRuleSchedules (inputWidth : Nat) (outputWidth : Nat)
    (layout : Fin outputWidth → BitSource inputWidth)
    for body inputWidth outputWidth layout
    with childContracts inputWidth outputWidth layout
    implementing cycleContract inputWidth outputWidth layout where
  output
    | .apply => [.split => Composition.SignalComponentRule.apply,
      .falseBit => Primitives.ConstantRule.apply,
      .trueBit => Primitives.ConstantRule.apply,
      .combine => Composition.SignalComponentRule.apply]
  state := []

section LayerCertification

variable (inputWidth outputWidth : Nat)
  (layout : Fin outputWidth → BitSource inputWidth)
  (children : ChildStructures (body inputWidth outputWidth layout)
    (childContracts inputWidth outputWidth layout))

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure
    (body inputWidth outputWidth layout) children

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure inputWidth outputWidth layout children).State) : Prop :=
  True

private theorem implements : Contracts.Cycle.Implements
    (certificationStructure inputWidth outputWidth layout children)
    (cycleContract inputWidth outputWidth layout)
    (stateCorresponds inputWidth outputWidth layout children) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  derive_empty_state_child_matches childMatch from
    children, inputs, structuralState, proposal, satisfies
  have splitValue := ((splitter inputWidth).outputRule_holds_iff _ _ _).mp
    ((childMatch .split).1.1 Composition.SignalComponentRule.apply)
  have falseValue := (Primitives.constantOutputRule_holds_iff false _ _ _).mp
    ((childMatch .falseBit).1.1 Primitives.ConstantRule.apply)
  have trueValue := (Primitives.constantOutputRule_holds_iff true _ _ _).mp
    ((childMatch .trueBit).1.1 Primitives.ConstantRule.apply)
  have combineValue := ((combiner outputWidth).outputRule_holds_iff _ _ _).mp
    ((childMatch .combine).1.1 Composition.SignalComponentRule.apply)
  have splitBit (index : Fin inputWidth) :
      (proposal.2 .split).outputs index = inputs .input index := by
    have equation := congrFun splitValue index
    simpa [Composition.SignalSplitter.outputValues, splitter,
      ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, SignalSource.value] using equation
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [applyRule_holds_iff]
    rw [show proposal.outputs .output =
        (proposal.2 .combine).outputs .value by exact boundary .output]
    rw [combineValue]
    funext index
    cases source : layout index with
    | input sourceIndex =>
        simp [Composition.SignalCombiner.outputValues, combiner,
          ProposedValues.childInputs_apply, body, wiring, context,
          EndpointContext.instanceOutput, SignalSource.value,
          BitSource.IsInput, BitSource.inputIndex,
          VectorLayout.apply]
        rw [source]
        change (proposal.2 .split).outputs sourceIndex = inputs .input sourceIndex
        exact splitBit sourceIndex
    | constant value =>
        cases value <;>
          simp [Composition.SignalCombiner.outputValues, combiner,
            ProposedValues.childInputs_apply, body, wiring, context,
            EndpointContext.instanceOutput, SignalSource.value,
            source, BitSource.IsInput, VectorLayout.apply,
            falseValue, trueValue]
  · rfl

end LayerCertification

module_cycle_certification certification (inputWidth : Nat) (outputWidth : Nat)
    (layout : Fin outputWidth → BitSource inputWidth)
    for moduleStructure inputWidth outputWidth layout
    via body inputWidth outputWidth layout
    with childContracts inputWidth outputWidth layout
    implementing cycleContract inputWidth outputWidth layout where
  schedules := derivedRuleSchedules inputWidth outputWidth layout,
  structuralChildren := structuralChildren inputWidth outputWidth layout,
  certifiedChildren := certifiedChildren inputWidth outputWidth layout,
  structuresMatch := certifiedChildren_moduleStructure inputWidth outputWidth layout,
  stateCorresponds := stateCorresponds inputWidth outputWidth layout,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements inputWidth outputWidth layout

end Silean.Modules.VectorLayout
