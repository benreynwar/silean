import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Examples.Fixtures.DualNot
import Silean.Examples.Fixtures.HierarchicalDualNot

namespace Silean.Examples.Checks.HierarchicalDualNotCertification

open Silean

private theorem forwardRule_holds_iff (inputs : Examples.Fixtures.DualNot.ports.inputs.Values)
    (state : Examples.Fixtures.DualNot.cycleContract.state.Values)
    (outputs : Examples.Fixtures.DualNot.ports.outputs.Values) :
    Examples.Fixtures.DualNot.forwardRule.Holds inputs state outputs ↔
      outputs .forward = !inputs .forward := by
  simp [Contracts.Cycle.CycleOutputRule.Holds, Examples.Fixtures.DualNot.forwardRule,
    SignalSelection.Matches, SignalSelection.project, SignalMap.select]

private theorem backwardRule_holds_iff (inputs : Examples.Fixtures.DualNot.ports.inputs.Values)
    (state : Examples.Fixtures.DualNot.cycleContract.state.Values)
    (outputs : Examples.Fixtures.DualNot.ports.outputs.Values) :
    Examples.Fixtures.DualNot.backwardRule.Holds inputs state outputs ↔
      outputs .backward = !inputs .backward := by
  simp [Contracts.Cycle.CycleOutputRule.Holds, Examples.Fixtures.DualNot.backwardRule,
    SignalSelection.Matches, SignalSelection.project, SignalMap.select]

private def stateCorresponds (_ : Examples.Fixtures.DualNot.cycleContract.state.Values)
    (_ : Examples.Fixtures.HierarchicalDualNot.moduleStructure.State) : Prop := True

private theorem implements : Contracts.Cycle.Implements Examples.Fixtures.HierarchicalDualNot.moduleStructure
    Examples.Fixtures.DualNot.cycleContract stateCorresponds := by
  intro inputs contractState structuralState proposal corresponds satisfies
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro name
    rcases proposal with ⟨outputs, children⟩
    rcases satisfies with ⟨boundary, childSatisfies⟩
    cases name
    · change Examples.Fixtures.DualNot.forwardRule.Holds inputs contractState _
      rw [forwardRule_holds_iff]
      have boundary' := boundary Examples.Fixtures.DualNot.Output.forward
      have child := (childSatisfies Examples.Fixtures.HierarchicalDualNot.Instance.forwardNot).1
      simpa [ProposedValues.outputs, ProposedValues.boundaryOutputsSatisfy,
        ProposedValues.childInputs, Examples.Fixtures.HierarchicalDualNot.body,
        Examples.Fixtures.HierarchicalDualNot.wiring, Examples.Fixtures.HierarchicalDualNot.context,
        Examples.Fixtures.HierarchicalDualNot.instancePorts,
        Examples.Fixtures.HierarchicalDualNot.moduleStructure,
        Examples.Fixtures.HierarchicalDualNot.childStructure, EndpointContext.moduleInput,
        EndpointContext.instanceOutput, SignalSource.value,
        Primitive.OutputsSatisfy, Primitives.not] using
          boundary'.trans (congrFun child .output)
    · change Examples.Fixtures.DualNot.backwardRule.Holds inputs contractState _
      rw [backwardRule_holds_iff]
      have boundary' := boundary Examples.Fixtures.DualNot.Output.backward
      have child := (childSatisfies Examples.Fixtures.HierarchicalDualNot.Instance.backwardNot).1
      simpa [ProposedValues.outputs, ProposedValues.boundaryOutputsSatisfy,
        ProposedValues.childInputs, Examples.Fixtures.HierarchicalDualNot.body,
        Examples.Fixtures.HierarchicalDualNot.wiring, Examples.Fixtures.HierarchicalDualNot.context,
        Examples.Fixtures.HierarchicalDualNot.instancePorts,
        Examples.Fixtures.HierarchicalDualNot.moduleStructure,
        Examples.Fixtures.HierarchicalDualNot.childStructure, EndpointContext.moduleInput,
        EndpointContext.instanceOutput, SignalSource.value,
        Primitive.OutputsSatisfy, Primitives.not] using
          boundary'.trans (congrFun child .output)
  · rfl

private theorem hasStructuralResult
    (inputs : Examples.Fixtures.DualNot.ports.inputs.Values)
    (currentState : Examples.Fixtures.HierarchicalDualNot.moduleStructure.State) :
    ∃ proposal, Examples.Fixtures.HierarchicalDualNot.moduleStructure.IsSolution
      inputs currentState proposal := by
  let forwardInputs : Primitives.not.ports.inputs.Values :=
    fun | .input => inputs .forward
  let backwardInputs : Primitives.not.ports.inputs.Values :=
    fun | .input => inputs .backward
  rcases Primitives.notCertified.hasStructuralResult forwardInputs
      (currentState .forwardNot) with ⟨forwardProposal, forwardSatisfies⟩
  rcases Primitives.notCertified.hasStructuralResult backwardInputs
      (currentState .backwardNot) with ⟨backwardProposal, backwardSatisfies⟩
  let childProposal : (name : Examples.Fixtures.HierarchicalDualNot.Instance) →
      ProposedValues (Examples.Fixtures.HierarchicalDualNot.childStructure name)
    | .forwardNot => forwardProposal
    | .backwardNot => backwardProposal
  let outputs : Examples.Fixtures.DualNot.ports.outputs.Values := fun
    | .forward => forwardProposal.outputs .output
    | .backward => backwardProposal.outputs .output
  refine ⟨ProposedValues.composite outputs childProposal, ?_⟩
  constructor
  · intro output
    cases output <;> rfl
  · intro child
    cases child with
    | forwardNot =>
        change Primitives.notCertified.moduleStructure.IsSolution
          (ProposedValues.childInputs Examples.Fixtures.HierarchicalDualNot.body
            Examples.Fixtures.HierarchicalDualNot.childStructure inputs childProposal .forwardNot)
          (currentState .forwardNot) forwardProposal
        rw [show ProposedValues.childInputs Examples.Fixtures.HierarchicalDualNot.body
          Examples.Fixtures.HierarchicalDualNot.childStructure inputs childProposal .forwardNot =
            forwardInputs by funext port; cases port; rfl]
        exact forwardSatisfies
    | backwardNot =>
        change Primitives.notCertified.moduleStructure.IsSolution
          (ProposedValues.childInputs Examples.Fixtures.HierarchicalDualNot.body
            Examples.Fixtures.HierarchicalDualNot.childStructure inputs childProposal .backwardNot)
          (currentState .backwardNot) backwardProposal
        rw [show ProposedValues.childInputs Examples.Fixtures.HierarchicalDualNot.body
          Examples.Fixtures.HierarchicalDualNot.childStructure inputs childProposal .backwardNot =
            backwardInputs by funext port; cases port; rfl]
        exact backwardSatisfies

open Silean.Contracts.Cycle.Certification.Layer

private abbrev childContracts :=
  Examples.Fixtures.HierarchicalDualNot.childContracts

private abbrev layerChildren :=
  Examples.Fixtures.HierarchicalDualNot.children

abbrev forwardOccurrence :
    RuleOccurrence Examples.Fixtures.HierarchicalDualNot.body childContracts :=
  ⟨Examples.Fixtures.HierarchicalDualNot.Instance.forwardNot, Primitives.NotRule.apply⟩

abbrev backwardOccurrence :
    RuleOccurrence Examples.Fixtures.HierarchicalDualNot.body childContracts :=
  ⟨Examples.Fixtures.HierarchicalDualNot.Instance.backwardNot, Primitives.NotRule.apply⟩

def scheduleOrders : ScheduleDerivation.RuleScheduleOrders
    Examples.Fixtures.HierarchicalDualNot.body childContracts
    Examples.Fixtures.DualNot.cycleContract where
  output
    | .forward => [forwardOccurrence]
    | .backward => [backwardOccurrence]
  state := []

def derivedRuleSchedules : ScheduleDerivation.DerivedRuleSchedules
    Examples.Fixtures.HierarchicalDualNot.body childContracts
    Examples.Fixtures.DualNot.cycleContract := by
  derive_rule_schedules scheduleOrders

abbrev ruleSchedules := derivedRuleSchedules.schedules

theorem coversChildren : ruleSchedules.CoversChildren :=
  derivedRuleSchedules.coversChildren



theorem hasAtMostOneSolution :
    Examples.Fixtures.HierarchicalDualNot.moduleStructure.HasAtMostOneSolution :=
  ruleSchedules.hasAtMostOneSolution coversChildren layerChildren

def dualNotCertified : Contracts.Cycle.ModuleCycleCertified Examples.Fixtures.DualNot.ports where
  moduleStructure := Examples.Fixtures.HierarchicalDualNot.moduleStructure
  cycleContract := Examples.Fixtures.DualNot.cycleContract
  certification := {
    stateCorresponds := stateCorresponds,
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩,
    hasStructuralResult := hasStructuralResult,
    structuralResultUnique := hasAtMostOneSolution,
    implements := implements }

end Silean.Examples.Checks.HierarchicalDualNotCertification
