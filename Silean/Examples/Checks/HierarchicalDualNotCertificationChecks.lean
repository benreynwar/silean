import Silean.CertifiedSchedule
import Silean.Examples.Fixtures.DualNot
import Silean.Examples.Fixtures.HierarchicalDualNot

namespace Silean.Examples.Checks.HierarchicalDualNotCertification

open Silean

private theorem forwardRule_holds_iff (inputs : Examples.Fixtures.DualNot.ports.inputs.Values)
    (state : Examples.Fixtures.DualNot.cycleContract.state.Values)
    (outputs : Examples.Fixtures.DualNot.ports.outputs.Values) :
    Examples.Fixtures.DualNot.forwardRule.Holds inputs state outputs ↔
      outputs .forward = !inputs .forward := by
  simp [CycleOutputRule.Holds, Examples.Fixtures.DualNot.forwardRule,
    SignalSelection.Matches, SignalSelection.project, SignalMap.select]

private theorem backwardRule_holds_iff (inputs : Examples.Fixtures.DualNot.ports.inputs.Values)
    (state : Examples.Fixtures.DualNot.cycleContract.state.Values)
    (outputs : Examples.Fixtures.DualNot.ports.outputs.Values) :
    Examples.Fixtures.DualNot.backwardRule.Holds inputs state outputs ↔
      outputs .backward = !inputs .backward := by
  simp [CycleOutputRule.Holds, Examples.Fixtures.DualNot.backwardRule,
    SignalSelection.Matches, SignalSelection.project, SignalMap.select]

private def stateCorresponds (_ : Examples.Fixtures.DualNot.cycleContract.state.Values)
    (_ : Examples.Fixtures.HierarchicalDualNot.moduleStructure.State) : Prop := True

private theorem implements : Implements Examples.Fixtures.HierarchicalDualNot.moduleStructure
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
        Examples.Fixtures.HierarchicalDualNot.instances,
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
        Examples.Fixtures.HierarchicalDualNot.instances,
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

open Silean.Certified

abbrev forwardOccurrence :
    RuleOccurrence Examples.Fixtures.HierarchicalDualNot.children :=
  ⟨Examples.Fixtures.HierarchicalDualNot.Instance.forwardNot, Primitives.NotRule.apply⟩

abbrev backwardOccurrence :
    RuleOccurrence Examples.Fixtures.HierarchicalDualNot.children :=
  ⟨Examples.Fixtures.HierarchicalDualNot.Instance.backwardNot, Primitives.NotRule.apply⟩

@[simp] theorem forwardOccurrence_reads : forwardOccurrence.reads = [.input] := rfl
@[simp] theorem forwardOccurrence_writes : forwardOccurrence.writes = [.output] := rfl
@[simp] theorem backwardOccurrence_reads : backwardOccurrence.reads = [.input] := rfl
@[simp] theorem backwardOccurrence_writes : backwardOccurrence.writes = [.output] := rfl
@[simp] theorem dualForward_reads :
    ((Examples.Fixtures.DualNot.cycleContract.outputRule Examples.Fixtures.DualNot.Rule.forward).2
      |>.readsInputs.labels) = [.forward] := rfl
@[simp] theorem dualForward_writes :
    ((Examples.Fixtures.DualNot.cycleContract.outputRule Examples.Fixtures.DualNot.Rule.forward).2
      |>.writesOutputs.labels) = [.forward] := rfl
@[simp] theorem dualBackward_reads :
    ((Examples.Fixtures.DualNot.cycleContract.outputRule Examples.Fixtures.DualNot.Rule.backward).2
      |>.readsInputs.labels) = [.backward] := rfl
@[simp] theorem dualBackward_writes :
    ((Examples.Fixtures.DualNot.cycleContract.outputRule Examples.Fixtures.DualNot.Rule.backward).2
      |>.writesOutputs.labels) = [.backward] := rfl

def forwardSchedule : OutputSchedule Examples.Fixtures.HierarchicalDualNot.body
    Examples.Fixtures.HierarchicalDualNot.children Examples.Fixtures.DualNot.cycleContract .forward :=
  .call forwardOccurrence
    (by
      intro port member
      cases port
      change Examples.Fixtures.DualNot.Input.forward ∈
        (Examples.Fixtures.DualNot.cycleContract.outputRule .forward).2.readsInputs.labels
      simp)
    (by simp)
  (.done (by
    intro output member
    cases output with
    | forward =>
        change outputAvailable [forwardOccurrence] .forwardNot .output
        exact ⟨Primitives.NotRule.apply, by simp, by simp⟩
    | backward =>
        simp at member))

def backwardSchedule : OutputSchedule Examples.Fixtures.HierarchicalDualNot.body
    Examples.Fixtures.HierarchicalDualNot.children Examples.Fixtures.DualNot.cycleContract .backward :=
  .call backwardOccurrence
    (by
      intro port member
      cases port
      change Examples.Fixtures.DualNot.Input.backward ∈
        (Examples.Fixtures.DualNot.cycleContract.outputRule .backward).2.readsInputs.labels
      simp)
    (by simp)
  (.done (by
    intro output member
    cases output with
    | forward =>
        simp at member
    | backward =>
        change outputAvailable [backwardOccurrence] .backwardNot .output
        exact ⟨Primitives.NotRule.apply, by simp, by simp⟩))

def stateSchedule : StateSchedule Examples.Fixtures.HierarchicalDualNot.body
    Examples.Fixtures.HierarchicalDualNot.children :=
  .done (by
    intro child input member
    cases child <;>
      simp [Examples.Fixtures.HierarchicalDualNot.children, Primitives.notCertified,
        Primitives.notCycleContract, CycleStateRule.empty,
        SignalSelection.labels] at member)

def ruleSchedules : RuleSchedules Examples.Fixtures.HierarchicalDualNot.body
    Examples.Fixtures.HierarchicalDualNot.children Examples.Fixtures.DualNot.cycleContract where
  output
    | .forward => forwardSchedule
    | .backward => backwardSchedule
  state := stateSchedule

theorem coversChildren : ruleSchedules.CoversChildren := by
  intro child rule
  cases child <;> cases rule
  · apply RuleSchedules.Combined.add_preserves
    apply RuleSchedules.mem_combineOutputs ruleSchedules .forward
    change forwardOccurrence ∈ forwardSchedule.finalAvailability
    simp [forwardSchedule, Schedule.finalAvailability]
  · apply RuleSchedules.Combined.add_preserves
    apply RuleSchedules.mem_combineOutputs ruleSchedules .backward
    change backwardOccurrence ∈ backwardSchedule.finalAvailability
    simp [backwardSchedule, Schedule.finalAvailability]

theorem hasAtMostOneSolution :
    Examples.Fixtures.HierarchicalDualNot.moduleStructure.HasAtMostOneSolution :=
  ruleSchedules.hasAtMostOneSolution coversChildren

def dualNotCertified : ModuleCycleCertified Examples.Fixtures.DualNot.ports where
  moduleStructure := Examples.Fixtures.HierarchicalDualNot.moduleStructure
  cycleContract := Examples.Fixtures.DualNot.cycleContract
  certification := {
    stateCorresponds := stateCorresponds,
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩,
    hasStructuralResult := hasStructuralResult,
    structuralResultUnique := hasAtMostOneSolution,
    implements := implements }

end Silean.Examples.Checks.HierarchicalDualNotCertification
