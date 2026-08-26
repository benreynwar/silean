import Silean2.CertifiedSchedule
import Silean2.Examples.DualNot
import Silean2.Examples.HierarchicalDualNot

namespace Silean2.Examples.ModuleCycleCertified

open Silean2

private theorem forwardRule_holds_iff (inputs : Examples.DualNot.ports.inputs.Values)
    (state : Examples.DualNot.cycleContract.state.Values)
    (outputs : Examples.DualNot.ports.outputs.Values) :
    Examples.DualNot.forwardRule.Holds inputs state outputs ↔
      outputs .forward = !inputs .forward := by
  simp [CycleOutputRule.Holds, Examples.DualNot.forwardRule,
    SignalSelection.Matches, SignalSelection.project, SignalMap.select]

private theorem backwardRule_holds_iff (inputs : Examples.DualNot.ports.inputs.Values)
    (state : Examples.DualNot.cycleContract.state.Values)
    (outputs : Examples.DualNot.ports.outputs.Values) :
    Examples.DualNot.backwardRule.Holds inputs state outputs ↔
      outputs .backward = !inputs .backward := by
  simp [CycleOutputRule.Holds, Examples.DualNot.backwardRule,
    SignalSelection.Matches, SignalSelection.project, SignalMap.select]

private def stateCorresponds (_ : Examples.DualNot.cycleContract.state.Values)
    (_ : Examples.HierarchicalDualNot.moduleStructure.State) : Prop := True

private theorem implements : Implements Examples.HierarchicalDualNot.moduleStructure
    Examples.DualNot.cycleContract stateCorresponds := by
  intro inputs contractState structuralState proposal corresponds satisfies
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro name
    rcases proposal with ⟨outputs, children⟩
    rcases satisfies with ⟨boundary, childSatisfies⟩
    cases name
    · change Examples.DualNot.forwardRule.Holds inputs contractState _
      rw [forwardRule_holds_iff]
      have boundary' := boundary Examples.DualNot.Output.forward
      have child := (childSatisfies Examples.HierarchicalDualNot.Instance.forwardNot).1
      simpa [ProposedValues.outputs, ProposedValues.boundaryOutputsSatisfy,
        ProposedValues.childInputs, Examples.HierarchicalDualNot.body,
        Examples.HierarchicalDualNot.wiring, Examples.HierarchicalDualNot.context,
        Examples.HierarchicalDualNot.instances,
        Examples.HierarchicalDualNot.moduleStructure,
        Examples.HierarchicalDualNot.childStructure, EndpointContext.moduleInput,
        EndpointContext.instanceOutput, SignalSource.value,
        Primitive.OutputsSatisfy, Primitives.not] using
          boundary'.trans (congrFun child .output)
    · change Examples.DualNot.backwardRule.Holds inputs contractState _
      rw [backwardRule_holds_iff]
      have boundary' := boundary Examples.DualNot.Output.backward
      have child := (childSatisfies Examples.HierarchicalDualNot.Instance.backwardNot).1
      simpa [ProposedValues.outputs, ProposedValues.boundaryOutputsSatisfy,
        ProposedValues.childInputs, Examples.HierarchicalDualNot.body,
        Examples.HierarchicalDualNot.wiring, Examples.HierarchicalDualNot.context,
        Examples.HierarchicalDualNot.instances,
        Examples.HierarchicalDualNot.moduleStructure,
        Examples.HierarchicalDualNot.childStructure, EndpointContext.moduleInput,
        EndpointContext.instanceOutput, SignalSource.value,
        Primitive.OutputsSatisfy, Primitives.not] using
          boundary'.trans (congrFun child .output)
  · rfl

private theorem hasStructuralResult
    (inputs : Examples.DualNot.ports.inputs.Values)
    (currentState : Examples.HierarchicalDualNot.moduleStructure.State) :
    ∃ proposal, Examples.HierarchicalDualNot.moduleStructure.IsSolution
      inputs currentState proposal := by
  let forwardInputs : Primitives.not.ports.inputs.Values :=
    fun | .input => inputs .forward
  let backwardInputs : Primitives.not.ports.inputs.Values :=
    fun | .input => inputs .backward
  rcases Primitives.notCertified.hasStructuralResult forwardInputs
      (currentState .forwardNot) with ⟨forwardProposal, forwardSatisfies⟩
  rcases Primitives.notCertified.hasStructuralResult backwardInputs
      (currentState .backwardNot) with ⟨backwardProposal, backwardSatisfies⟩
  let childProposal : (name : Examples.HierarchicalDualNot.Instance) →
      ProposedValues (Examples.HierarchicalDualNot.childStructure name)
    | .forwardNot => forwardProposal
    | .backwardNot => backwardProposal
  let outputs : Examples.DualNot.ports.outputs.Values := fun
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
          (ProposedValues.childInputs Examples.HierarchicalDualNot.body
            Examples.HierarchicalDualNot.childStructure inputs childProposal .forwardNot)
          (currentState .forwardNot) forwardProposal
        rw [show ProposedValues.childInputs Examples.HierarchicalDualNot.body
          Examples.HierarchicalDualNot.childStructure inputs childProposal .forwardNot =
            forwardInputs by funext port; cases port; rfl]
        exact forwardSatisfies
    | backwardNot =>
        change Primitives.notCertified.moduleStructure.IsSolution
          (ProposedValues.childInputs Examples.HierarchicalDualNot.body
            Examples.HierarchicalDualNot.childStructure inputs childProposal .backwardNot)
          (currentState .backwardNot) backwardProposal
        rw [show ProposedValues.childInputs Examples.HierarchicalDualNot.body
          Examples.HierarchicalDualNot.childStructure inputs childProposal .backwardNot =
            backwardInputs by funext port; cases port; rfl]
        exact backwardSatisfies

open Silean2.Certified

abbrev forwardOccurrence :
    RuleOccurrence Examples.HierarchicalDualNot.children :=
  ⟨Examples.HierarchicalDualNot.Instance.forwardNot, Primitives.NotRule.apply⟩

abbrev backwardOccurrence :
    RuleOccurrence Examples.HierarchicalDualNot.children :=
  ⟨Examples.HierarchicalDualNot.Instance.backwardNot, Primitives.NotRule.apply⟩

@[simp] theorem forwardOccurrence_reads : forwardOccurrence.reads = [.input] := rfl
@[simp] theorem forwardOccurrence_writes : forwardOccurrence.writes = [.output] := rfl
@[simp] theorem backwardOccurrence_reads : backwardOccurrence.reads = [.input] := rfl
@[simp] theorem backwardOccurrence_writes : backwardOccurrence.writes = [.output] := rfl
@[simp] theorem dualForward_reads :
    ((Examples.DualNot.cycleContract.outputRule Examples.DualNot.Rule.forward).2
      |>.readsInputs.labels) = [.forward] := rfl
@[simp] theorem dualForward_writes :
    ((Examples.DualNot.cycleContract.outputRule Examples.DualNot.Rule.forward).2
      |>.writesOutputs.labels) = [.forward] := rfl
@[simp] theorem dualBackward_reads :
    ((Examples.DualNot.cycleContract.outputRule Examples.DualNot.Rule.backward).2
      |>.readsInputs.labels) = [.backward] := rfl
@[simp] theorem dualBackward_writes :
    ((Examples.DualNot.cycleContract.outputRule Examples.DualNot.Rule.backward).2
      |>.writesOutputs.labels) = [.backward] := rfl

def forwardSchedule : OutputSchedule Examples.HierarchicalDualNot.body
    Examples.HierarchicalDualNot.children Examples.DualNot.cycleContract .forward :=
  .call forwardOccurrence
    (by
      intro port member
      cases port
      change Examples.DualNot.Input.forward ∈
        (Examples.DualNot.cycleContract.outputRule .forward).2.readsInputs.labels
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

def backwardSchedule : OutputSchedule Examples.HierarchicalDualNot.body
    Examples.HierarchicalDualNot.children Examples.DualNot.cycleContract .backward :=
  .call backwardOccurrence
    (by
      intro port member
      cases port
      change Examples.DualNot.Input.backward ∈
        (Examples.DualNot.cycleContract.outputRule .backward).2.readsInputs.labels
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

def stateSchedule : StateSchedule Examples.HierarchicalDualNot.body
    Examples.HierarchicalDualNot.children :=
  .done trivial

def ruleSchedules : RuleSchedules Examples.HierarchicalDualNot.body
    Examples.HierarchicalDualNot.children Examples.DualNot.cycleContract where
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
    Examples.HierarchicalDualNot.moduleStructure.HasAtMostOneSolution :=
  ruleSchedules.hasAtMostOneSolution coversChildren

def dualNotCertified : ModuleCycleCertified Examples.DualNot.ports where
  moduleStructure := Examples.HierarchicalDualNot.moduleStructure
  cycleContract := Examples.DualNot.cycleContract
  stateCorresponds := stateCorresponds
  hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
  hasStructuralResult := hasStructuralResult
  structuralResultUnique := hasAtMostOneSolution
  implements := implements

end Silean2.Examples.ModuleCycleCertified
