import Silean.ModuleCycleContract
import Silean.SignalLayout

namespace Silean

namespace SignalSelection

def Matches (selection : SignalSelection signals types)
    (outputs : signals.Values) (selected : types.Denote) : Prop :=
  match selection with
  | .nil => True
  | .cons label tail =>
      outputs label = selected.1 ∧ tail.Matches outputs selected.2

theorem matches_project (selection : SignalSelection signals types)
    (values : signals.Values) : selection.Matches values (selection.project values) := by
  induction selection with
  | nil => trivial
  | cons label tail induction => exact ⟨rfl, induction⟩

private def write (selection : SignalSelection signals types)
    (original : signals.Values) (selected : types.Denote) :
    signals.Values :=
  match selection with
  | .nil => original
  | .cons label tail =>
      signals.set (tail.write original selected.2) label selected.1

private theorem write_eq_of_not_mem
    (selection : SignalSelection signals types)
    (original : signals.Values) (selected : types.Denote)
    (label : signals.Label) (notMember : label ∉ selection.labels) :
    selection.write original selected label = original label := by
  induction selection with
  | nil => rfl
  | cons head tail induction =>
      have different : label ≠ head := fun equal =>
        notMember (equal ▸ List.Mem.head tail.labels)
      rw [write, SignalMap.set_other _ _ _ _ different]
      exact induction selected.2 fun member =>
        notMember (List.Mem.tail head member)

private theorem Matches.of_eq_on
    (selection : SignalSelection signals types)
    {left right : signals.Values} {selected : types.Denote}
    (holds : selection.Matches left selected)
    (equal : ∀ label, label ∈ selection.labels → left label = right label) :
    selection.Matches right selected := by
  induction selection with
  | nil => trivial
  | cons head tail induction =>
      constructor
      · exact (equal head (List.Mem.head _)).symm.trans holds.1
      · exact induction holds.2 fun label member =>
          equal label (List.Mem.tail head member)

theorem Matches.eq_of_mem
    (selection : SignalSelection signals types)
    {left right : signals.Values} {selected : types.Denote}
    (leftMatches : selection.Matches left selected)
    (rightMatches : selection.Matches right selected)
    (label : signals.Label) (member : label ∈ selection.labels) :
    left label = right label := by
  induction selection with
  | nil => cases member
  | cons head tail induction =>
      rcases List.mem_cons.mp member with equal | member
      · subst label
        exact leftMatches.1.trans rightMatches.1.symm
      · exact induction leftMatches.2 rightMatches.2 member

theorem allSelection_matches_project_iff (signals : SignalMap)
    (left right : signals.Values) :
    signals.allSelection.Matches left
      (signals.allSelection.project right) ↔ left = right := by
  constructor
  · intro holds
    funext label
    exact SignalSelection.Matches.eq_of_mem signals.allSelection
      holds (signals.allSelection.matches_project right) label
      (by
        rw [SignalMap.allSelection_labels]
        exact ListIndex.get_eq (signals.labels.locate label) ▸
          List.get_mem _ _)
  · intro equal
    subst left
    exact signals.allSelection.matches_project right

theorem project_eq_of_eq_on
    (selection : SignalSelection signals types)
    (left right : signals.Values)
    (equal : ∀ label, label ∈ selection.labels → left label = right label) :
    selection.project left = selection.project right := by
  induction selection with
  | nil => rfl
  | cons head tail induction =>
      simp only [project]
      rw [equal head (List.Mem.head _)]
      rw [induction fun label member => equal label (List.Mem.tail head member)]

private theorem write_matches (selection : SignalSelection signals types)
    (original : signals.Values) (selected : types.Denote)
    (nodup : selection.labels.Nodup) :
    selection.Matches (selection.write original selected) selected := by
  induction selection with
  | nil => trivial
  | cons head tail induction =>
      have parts := List.nodup_cons.mp nodup
      have headNotMem : head ∉ tail.labels := parts.1
      have tailNodup : tail.labels.Nodup := parts.2
      constructor
      · exact SignalMap.set_same _ _ _
      · apply Matches.of_eq_on tail (induction selected.2 tailNodup)
        intro label member
        exact (SignalMap.set_other _ _ _ _ fun equal => by
          subst label
          exact headNotMem member).symm

end SignalSelection

private structure SignalAssignment (signals : SignalMap) where
  types : SignalTypes
  selection : SignalSelection signals types
  selected : types.Denote

namespace SignalAssignment

private def labels (assignment : SignalAssignment signals) : List signals.Label :=
  assignment.selection.labels

private def apply (assignment : SignalAssignment signals)
    (original : signals.Values) : signals.Values :=
  assignment.selection.write original assignment.selected

private def Matches (assignment : SignalAssignment signals)
    (outputs : signals.Values) : Prop :=
  assignment.selection.Matches outputs assignment.selected

private theorem apply_matches (assignment : SignalAssignment signals)
    (original : signals.Values) (nodup : assignment.labels.Nodup) :
    assignment.Matches (assignment.apply original) :=
  assignment.selection.write_matches original assignment.selected nodup

private theorem apply_preserves
    (assignment : SignalAssignment signals)
    (existing : SignalAssignment signals)
    (outputs : signals.Values)
    (holds : existing.Matches outputs)
    (disjoint : ∀ left, left ∈ assignment.labels →
      ∀ right, right ∈ existing.labels → left ≠ right) :
    existing.Matches (assignment.apply outputs) := by
  apply SignalSelection.Matches.of_eq_on existing.selection holds
  intro label member
  exact (assignment.selection.write_eq_of_not_mem outputs assignment.selected
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

namespace CycleOutputRule

private def assignment (rule : CycleOutputRule ports state shape)
    (inputs : ports.inputs.Values) (currentState : state.Values) :
    SignalAssignment ports.outputs where
  types := shape.outputTypes
  selection := rule.writesOutputs
  selected := rule.target (rule.readsInputs.project inputs) currentState

def Holds (rule : CycleOutputRule ports state shape)
    (inputs : ports.inputs.Values) (currentState : state.Values)
    (outputs : ports.outputs.Values) : Prop :=
  rule.writesOutputs.Matches outputs
    (rule.target (rule.readsInputs.project inputs) currentState)

end CycleOutputRule

namespace ModuleCycleContract

private def assignments (contract : ModuleCycleContract ports)
    (inputs : ports.inputs.Values) (currentState : contract.state.Values) :
    List (SignalAssignment ports.outputs) :=
  contract.ruleNames.values.map fun name =>
    (contract.outputRule name).2.assignment inputs currentState

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
  ∀ name, (contract.outputRule name).2.Holds inputs currentState outputs

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
  change ((contract.outputRule name).2.assignment inputs currentState).Matches
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
  exact SignalSelection.Matches.eq_of_mem
    (contract.outputRule name).2.writesOutputs
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

end ModuleCycleContract

end Silean
