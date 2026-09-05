import Silean.Contracts.Cycle.CycleContract

namespace Silean

open Contracts.Cycle

/-! Defines what it means for outputs and next state to satisfy a cycle
contract, then derives the contract's deterministic `evaluate` function. This
evaluation is behavioral and does not execute a module structure. -/

private structure SignalAssignment (signals : SignalMap) where
  group : SignalGroup signals
  selected : group.signals.Values

namespace SignalAssignment

private def labels (assignment : SignalAssignment signals) : List signals.Label :=
  assignment.group.labels

private def apply (assignment : SignalAssignment signals)
    (original : signals.Values) : signals.Values :=
  assignment.group.write original assignment.selected

private def Matches (assignment : SignalAssignment signals)
    (outputs : signals.Values) : Prop :=
  assignment.group.Matches outputs assignment.selected

private theorem apply_matches (assignment : SignalAssignment signals)
    (original : signals.Values) (nodup : assignment.labels.Nodup) :
    assignment.Matches (assignment.apply original) :=
  assignment.group.write_matches original assignment.selected nodup

private theorem apply_preserves
    (assignment : SignalAssignment signals)
    (existing : SignalAssignment signals)
    (outputs : signals.Values)
    (holds : existing.Matches outputs)
    (disjoint : ∀ left, left ∈ assignment.labels →
      ∀ right, right ∈ existing.labels → left ≠ right) :
    existing.Matches (assignment.apply outputs) := by
  apply SignalGroup.Matches.of_eq_on existing.group holds
  intro label member
  exact (assignment.group.write_eq_of_not_mem outputs assignment.selected
    label fun written => disjoint label written label member rfl).symm

end SignalAssignment

namespace AssignmentList

private def labels (assignments : List (SignalAssignment signals)) : List signals.Label :=
  assignments.flatMap SignalAssignment.labels

private def applyAll (assignments : List (SignalAssignment signals))
    (original : signals.Values) : signals.Values :=
  match assignments with
  | [] => original
  | assignment :: rest => assignment.apply (applyAll rest original)

private theorem applyAll_matches
    (assignments : List (SignalAssignment signals))
    (original : signals.Values) (nodup : (labels assignments).Nodup)
    (assignment : SignalAssignment signals) (member : assignment ∈ assignments) :
    assignment.Matches (applyAll assignments original) := by
  induction assignments with
  | nil => cases member
  | cons head tail induction =>
      have parts := List.nodup_append.mp nodup
      rcases List.mem_cons.mp member with equal | member
      · cases equal
        exact SignalAssignment.apply_matches assignment (applyAll tail original) parts.1
      · apply head.apply_preserves assignment (applyAll tail original)
          (induction parts.2.1 member)
        intro left leftMember right rightMember
        exact parts.2.2 left leftMember right
          (List.mem_flatMap.mpr ⟨assignment, member, rightMember⟩)

end AssignmentList

namespace Contracts.Cycle.CycleOutputRule

private def assignment (rule : CycleOutputRule ports state)
    (inputs : ports.inputs.Values) (currentState : state.Values) :
    SignalAssignment ports.outputs where
  group := rule.writesOutputs
  selected := rule.target (rule.readsInputs.project inputs) currentState

def Holds (rule : CycleOutputRule ports state)
    (inputs : ports.inputs.Values) (currentState : state.Values)
    (outputs : ports.outputs.Values) : Prop :=
  rule.writesOutputs.Matches outputs
    (rule.target (rule.readsInputs.project inputs) currentState)

end Contracts.Cycle.CycleOutputRule

namespace Contracts.Cycle.ModuleCycleContract

private def assignments (contract : ModuleCycleContract ports)
    (inputs : ports.inputs.Values) (currentState : contract.state.Values) :
    List (SignalAssignment ports.outputs) :=
  contract.ruleNames.values.map fun name =>
    (contract.outputRule name).assignment inputs currentState

private theorem assignments_labels (contract : ModuleCycleContract ports)
    (inputs : ports.inputs.Values) (currentState : contract.state.Values) :
    AssignmentList.labels (contract.assignments inputs currentState) =
      contract.writtenOutputs := by
  simp [assignments, AssignmentList.labels, CycleOutputRule.assignment,
    SignalAssignment.labels, writtenOutputs, List.flatMap_map]

private theorem assignments_labels_nodup (contract : ModuleCycleContract ports)
    (inputs : ports.inputs.Values) (currentState : contract.state.Values) :
    (AssignmentList.labels (contract.assignments inputs currentState)).Nodup := by
  rw [contract.assignments_labels inputs currentState]
  exact contract.writtenOutputs_nodup

def OutputRulesHold (contract : ModuleCycleContract ports)
    (inputs : ports.inputs.Values) (currentState : contract.state.Values)
    (outputs : ports.outputs.Values) : Prop :=
  ∀ name, (contract.outputRule name).Holds inputs currentState outputs

def EvaluatesTo (contract : ModuleCycleContract ports)
    (inputs : ports.inputs.Values) (currentState : contract.state.Values)
    (outputs : ports.outputs.Values) (nextState : contract.state.Values) : Prop :=
  contract.OutputRulesHold inputs currentState outputs ∧
    nextState = contract.stateRule.apply inputs currentState

def applyOutputRules (contract : ModuleCycleContract ports)
    (inputs : ports.inputs.Values) (currentState : contract.state.Values) :
    ports.outputs.Values :=
  AssignmentList.applyAll (contract.assignments inputs currentState)
    ports.outputs.defaultValues

theorem applyOutputRules_hold (contract : ModuleCycleContract ports)
    (inputs : ports.inputs.Values) (currentState : contract.state.Values) :
    contract.OutputRulesHold inputs currentState
      (contract.applyOutputRules inputs currentState) := by
  intro name
  change ((contract.outputRule name).assignment inputs currentState).Matches
    (contract.applyOutputRules inputs currentState)
  apply AssignmentList.applyAll_matches
    (contract.assignments inputs currentState) ports.outputs.defaultValues
    (contract.assignments_labels_nodup inputs currentState)
  apply List.mem_map.mpr
  exact ⟨name, by
    exact ListIndex.get_eq (contract.ruleNames.locate name) ▸
      List.get_mem _ _, rfl⟩

def evaluate (contract : ModuleCycleContract ports)
    (inputs : ports.inputs.Values) (currentState : contract.state.Values) :
    ports.outputs.Values × contract.state.Values :=
  (contract.applyOutputRules inputs currentState,
    contract.stateRule.apply inputs currentState)

theorem evaluate_evaluatesTo (contract : ModuleCycleContract ports)
    (inputs : ports.inputs.Values) (currentState : contract.state.Values) :
    contract.EvaluatesTo inputs currentState
      (contract.evaluate inputs currentState).1
      (contract.evaluate inputs currentState).2 :=
  ⟨contract.applyOutputRules_hold inputs currentState, rfl⟩

theorem outputs_unique (contract : ModuleCycleContract ports)
    (inputs : ports.inputs.Values) (currentState : contract.state.Values)
    (left right : ports.outputs.Values)
    (leftSatisfies : contract.OutputRulesHold inputs currentState left)
    (rightSatisfies : contract.OutputRulesHold inputs currentState right) :
    left = right := by
  funext output
  have written := contract.output_is_written output
  rw [writtenOutputs] at written
  rcases List.mem_flatMap.mp written with ⟨name, nameMem, outputMem⟩
  exact SignalGroup.Matches.eq_of_mem
    (contract.outputRule name).writesOutputs
    (leftSatisfies name) (rightSatisfies name) output outputMem

theorem evaluation_unique (contract : ModuleCycleContract ports)
    (inputs : ports.inputs.Values) (currentState : contract.state.Values)
    (leftOutputs rightOutputs : ports.outputs.Values)
    (leftNext rightNext : contract.state.Values)
    (leftSatisfies : contract.EvaluatesTo inputs currentState leftOutputs leftNext)
    (rightSatisfies : contract.EvaluatesTo inputs currentState rightOutputs rightNext) :
    leftOutputs = rightOutputs ∧ leftNext = rightNext :=
  ⟨contract.outputs_unique inputs currentState leftOutputs rightOutputs
      leftSatisfies.1 rightSatisfies.1,
    leftSatisfies.2.trans rightSatisfies.2.symm⟩

end Contracts.Cycle.ModuleCycleContract

end Silean
