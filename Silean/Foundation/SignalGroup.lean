import Silean.Foundation.SignalMap

namespace Silean

/-! A label-preserving view of a group of signals inside a larger signal map. -/

/-- A named signal map embedded type-correctly into a parent signal map. Values
projected through a group retain the group's labels; the ordered embedded
labels are the dependency information used by schedules. Contracts separately
require output groups not to contain duplicate parent labels. -/
structure SignalGroup (parent : SignalMap.{0}) where
  signals : SignalMap.{0}
  embed : signals.Label → parent.Label
  preservesType : ∀ label,
    signals.signalType label = parent.signalType (embed label)

namespace SignalGroup

/-- Build a named group by mapping each of its labels to a parent label. The
group's signal types are inherited from the parent, so callers name the group
without repeating any `SignalType` information or proving type equalities. -/
@[reducible] def fromLabels (parent : SignalMap) (Label : Type)
    [Enumeration Label] (embed : Label → parent.Label) : SignalGroup parent where
  signals := EnumeratedMap.of Label fun label => parent.signalType (embed label)
  embed := embed
  preservesType := fun _ => rfl

/-- The parent labels selected by the group, in the group's canonical order. -/
def labels (group : SignalGroup parent) : List parent.Label :=
  group.signals.labels.values.map group.embed

private def castForward {left right : SignalType} (equal : left = right) :
    left.Denote → right.Denote := by
  cases equal
  exact id

private def castBackward {left right : SignalType} (equal : left = right) :
    right.Denote → left.Denote := by
  cases equal
  exact id

@[simp] private theorem castBackward_castForward {left right : SignalType}
    (equal : left = right) (value : left.Denote) :
    castBackward equal (castForward equal value) = value := by
  cases equal
  rfl

private theorem castBackward_injective {left right : SignalType}
    (equal : left = right) : Function.Injective (castBackward equal) := by
  cases equal
  exact Function.injective_id

private def projectedValue (group : SignalGroup parent)
    (label : group.signals.Label)
    (value : (parent.signalType (group.embed label)).Denote) :
    (group.signals.signalType label).Denote :=
  castBackward (group.preservesType label) value

/-- View parent values through the group's own named signal map. -/
def project (group : SignalGroup parent) (values : parent.Values) :
    group.signals.Values := fun label =>
  group.projectedValue label (values (group.embed label))

@[simp] theorem fromLabels_project_apply (parent : SignalMap) (Label : Type)
    [Enumeration Label] (embed : Label → parent.Label)
    (values : parent.Values) (label : Label) :
    (fromLabels parent Label embed).project values label =
      values (embed label) := rfl

private def embeddedValue (group : SignalGroup parent)
    (values : group.signals.Values) (label : group.signals.Label) :
    (parent.signalType (group.embed label)).Denote :=
  castForward (group.preservesType label) (values label)

@[simp] private theorem projectedValue_embeddedValue
    (group : SignalGroup parent) (values : group.signals.Values)
    (label : group.signals.Label) :
    group.projectedValue label (group.embeddedValue values label) = values label := by
  exact castBackward_castForward (group.preservesType label) (values label)

private theorem projectedValue_injective (group : SignalGroup parent)
    (label : group.signals.Label) :
    Function.Injective (group.projectedValue label) := by
  intro left right equal
  exact castBackward_injective (group.preservesType label) equal

/-- Selected values agree with a complete parent valuation. -/
def Matches (group : SignalGroup parent) (parentValues : parent.Values)
    (selectedValues : group.signals.Values) : Prop :=
  group.project parentValues = selectedValues

@[simp] theorem matches_project (group : SignalGroup parent)
    (values : parent.Values) : group.Matches values (group.project values) := rfl

@[simp] theorem fromLabels_matches_iff (parent : SignalMap) (Label : Type)
    [Enumeration Label] (embed : Label → parent.Label)
    (values : parent.Values)
    (selected : (fromLabels parent Label embed).signals.Values) :
    (fromLabels parent Label embed).Matches values selected ↔
      ∀ label, values (embed label) = selected label := by
  constructor
  · intro equal label
    exact congrFun equal label
  · intro equal
    funext label
    exact equal label

private def writeLabels (group : SignalGroup parent)
    (labels : List group.signals.Label) (original : parent.Values)
    (selected : group.signals.Values) : parent.Values :=
  match labels with
  | [] => original
  | label :: rest =>
      parent.set (group.writeLabels rest original selected)
        (group.embed label) (group.embeddedValue selected label)

/-- Replace the parent signals named by the group and retain all others. -/
def write (group : SignalGroup parent) (original : parent.Values)
    (selected : group.signals.Values) : parent.Values :=
  group.writeLabels group.signals.labels.values original selected

private theorem writeLabels_eq_of_not_mem (group : SignalGroup parent)
    (remaining : List group.signals.Label) (original : parent.Values)
    (selected : group.signals.Values) (label : parent.Label)
    (notMember : label ∉ remaining.map group.embed) :
    group.writeLabels remaining original selected label = original label := by
  induction remaining with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.map_cons, List.mem_cons, not_or] at notMember
      simp only [writeLabels]
      rw [SignalMap.set_other _ _ _ _ notMember.1]
      exact induction notMember.2

theorem write_eq_of_not_mem (group : SignalGroup parent)
    (original : parent.Values) (selected : group.signals.Values)
    (label : parent.Label) (notMember : label ∉ group.labels) :
    group.write original selected label = original label :=
  group.writeLabels_eq_of_not_mem group.signals.labels.values original selected
    label notMember

/-- The group containing the complete parent map with its existing labels. -/
@[reducible] def all (signals : SignalMap) : SignalGroup signals where
  signals := signals
  embed := id
  preservesType := fun _ => rfl

/-- The empty group inside any parent signal map. -/
@[reducible] def empty (signals : SignalMap) : SignalGroup signals where
  signals := emptySignalMap
  embed := fun label => nomatch label
  preservesType := fun label => nomatch label

@[simp] theorem all_labels (signals : SignalMap) :
    (all signals).labels = signals.labels.values := by
  simp [labels, all]

@[simp] theorem empty_labels (signals : SignalMap) :
    (empty signals).labels = [] := rfl

@[simp] theorem all_project (signals : SignalMap) (values : signals.Values) :
    (all signals).project values = values := by
  funext label
  simp [project, projectedValue, all, castBackward]

@[simp] theorem all_matches (signals : SignalMap) (left right : signals.Values) :
    (all signals).Matches left right ↔ left = right := by
  simp [Matches]

theorem project_eq_of_eq_on (group : SignalGroup parent)
    (left right : parent.Values)
    (equal : ∀ label, label ∈ group.labels → left label = right label) :
    group.project left = group.project right := by
  funext label
  apply congrArg (group.projectedValue label)
  apply equal
  exact List.mem_map.mpr ⟨label,
    ListIndex.get_eq (group.signals.labels.locate label) ▸ List.get_mem _ _, rfl⟩

theorem Matches.of_eq_on (group : SignalGroup parent)
    {left right : parent.Values} {selected : group.signals.Values}
    (holds : group.Matches left selected)
    (equal : ∀ label, label ∈ group.labels → left label = right label) :
    group.Matches right selected := by
  unfold Matches at holds ⊢
  rw [← holds]
  exact (group.project_eq_of_eq_on left right equal).symm

theorem Matches.eq_of_mem (group : SignalGroup parent)
    {left right : parent.Values} {selected : group.signals.Values}
    (leftMatches : group.Matches left selected)
    (rightMatches : group.Matches right selected)
    (label : parent.Label) (member : label ∈ group.labels) :
    left label = right label := by
  rcases List.mem_map.mp member with ⟨groupLabel, _, equal⟩
  subst label
  have projected := congrFun (leftMatches.trans rightMatches.symm) groupLabel
  exact group.projectedValue_injective groupLabel projected

private theorem project_writeLabels_of_mem (group : SignalGroup parent)
    (remaining : List group.signals.Label) (original : parent.Values)
    (selected : group.signals.Values)
    (label : group.signals.Label) (member : label ∈ remaining)
    (nodup : (remaining.map group.embed).Nodup) :
    group.project (group.writeLabels remaining original selected) label =
      selected label := by
  induction remaining with
  | nil => cases member
  | cons head tail induction =>
      have parts := List.nodup_cons.mp nodup
      by_cases equal : label = head
      · subst label
        simp [writeLabels, project]
      · simp only [writeLabels, project]
        rw [SignalMap.set_other _ _ _ _]
        · exact induction (List.mem_of_ne_of_mem equal member) parts.2
        · intro embeddedEqual
          apply parts.1
          rw [← embeddedEqual]
          exact List.mem_map.mpr
            ⟨label, List.mem_of_ne_of_mem equal member, rfl⟩

theorem write_matches (group : SignalGroup parent) (original : parent.Values)
    (selected : group.signals.Values) (nodup : group.labels.Nodup) :
    group.Matches (group.write original selected) selected := by
  unfold Matches write
  funext label
  apply group.project_writeLabels_of_mem
  · exact ListIndex.get_eq (group.signals.labels.locate label) ▸ List.get_mem _ _
  · exact nodup

end SignalGroup

end Silean
