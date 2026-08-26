import Silean2.ModuleCycleContract

namespace Silean2

/-! Shared machinery for viewing vectors and tuples as their immediate
components.  The public structural components that use this machinery are
closed to those two aggregate forms. -/

inductive SignalTypes.Position : SignalTypes → Type
  | head : Position (.cons head tail)
  | tail : Position tail → Position (.cons head tail)

namespace SignalTypes

def typeAt : (fields : SignalTypes) → Position fields → SignalType
  | .cons head _, .head => head
  | .cons _ tail, .tail position => typeAt tail position

theorem complexity_typeAt_lt : ∀ (fields : SignalTypes) (position : Position fields),
    (typeAt fields position).complexity < fields.complexity + 1
  | .cons _ _, .head => by simp [typeAt, complexity]; omega
  | .cons _ tail, .tail position => by
      have smaller := complexity_typeAt_lt tail position
      simp [typeAt, complexity] at smaller ⊢
      omega

@[reducible] def positions : (fields : SignalTypes) → Enumeration (Position fields)
  | .nil => Enumeration.empty fun position => nomatch position
  | .cons head tail =>
      let rest := positions tail
      { values := .head :: rest.values.map Position.tail
        nodup := by
          apply List.Pairwise.cons
          · intro value member equal
            rcases List.mem_map.mp member with ⟨position, _, rfl⟩
            cases equal
          · exact List.nodup_map_of_injective Position.tail
              (by intro left right equal; cases equal; rfl) rest.nodup
        locate
          | .head => .head
          | .tail position => .tail ((rest.locate position).map Position.tail) }

def componentMap (fields : SignalTypes) : SignalMap where
  Key := Position fields
  keys := positions fields
  value := typeAt fields

def get : (fields : SignalTypes) → fields.Denote →
    (position : Position fields) → (typeAt fields position).Denote
  | .cons _ _, (head, _), .head => head
  | .cons _ tail, (_, rest), .tail position => get tail rest position

def assemble : (fields : SignalTypes) →
    ((position : Position fields) → (typeAt fields position).Denote) →
      fields.Denote
  | .nil, _ => ()
  | .cons _ tail, values =>
      (values .head, assemble tail fun position => values (.tail position))

theorem get_assemble : ∀ (fields : SignalTypes)
    (values : (position : Position fields) → (typeAt fields position).Denote),
    get fields (assemble fields values) = values
  | .nil, values => by
      funext position
      exact nomatch position
  | .cons head tail, values => by
      funext position
      cases position with
      | head => rfl
      | tail position => exact congrFun (get_assemble tail _) position

theorem assemble_get : ∀ (fields : SignalTypes) (value : fields.Denote),
    assemble fields (get fields value) = value
  | .nil, value => by cases value; rfl
  | .cons head tail, value => by
      rcases value with ⟨headValue, tailValue⟩
      change (headValue, assemble tail (get tail tailValue)) = _
      rw [assemble_get tail]

end SignalTypes

namespace SignalType

@[reducible] def vectorComponents (length : Nat) (element : SignalType) : SignalMap :=
  {
    Key := Fin length
    keys := Enumeration.fin length
    value := fun _ => element }

end SignalType

namespace SignalMap

def selectionFrom (signals : SignalMap) :
    (labels : List signals.Label) →
      SignalSelection signals (.ofList (labels.map signals.signalType))
  | [] => .nil
  | label :: rest => .cons label (selectionFrom signals rest)

def allSelection (signals : SignalMap) :
    SignalSelection signals (.ofList signals.types) :=
  selectionFrom signals signals.labels.values

@[simp] theorem selectionFrom_labels (signals : SignalMap) :
    ∀ labels, (selectionFrom signals labels).labels = labels
  | [] => rfl
  | head :: rest => by
      change head :: (selectionFrom signals rest).labels = head :: rest
      rw [selectionFrom_labels]

@[simp] theorem allSelection_labels (signals : SignalMap) :
    signals.allSelection.labels = signals.labels.values :=
  selectionFrom_labels signals signals.labels.values

def unpackFrom (signals : SignalMap) :
    (labels : List signals.Label) →
      (SignalTypes.ofList (labels.map signals.signalType)).Denote → signals.Values
  | [], _ => signals.defaultValues
  | label :: rest, (head, tail) =>
      signals.set (unpackFrom signals rest tail) label head

def unpack (signals : SignalMap) :
    (SignalTypes.ofList signals.types).Denote → signals.Values :=
  unpackFrom signals signals.labels.values

theorem unpackFrom_project_eq_of_mem (signals : SignalMap)
    (labels : List signals.Label) (values : signals.Values)
    (label : signals.Label) (member : label ∈ labels) :
    unpackFrom signals labels (selectionFrom signals labels |>.project values) label =
      values label := by
  induction labels with
  | nil => cases member
  | cons head tail induction =>
      by_cases equal : label = head
      · subst head
        change signals.set
          (unpackFrom signals tail ((selectionFrom signals tail).project values))
          label (values label) label = values label
        exact SignalMap.set_same _ _ _
      · change signals.set
          (unpackFrom signals tail ((selectionFrom signals tail).project values))
          head (values head) label = values label
        rw [SignalMap.set_other _ _ _ _ equal]
        exact induction (List.mem_of_ne_of_mem equal member)

theorem unpack_project (signals : SignalMap) (values : signals.Values) :
    signals.unpack (signals.allSelection.project values) = values := by
  funext label
  apply unpackFrom_project_eq_of_mem
  exact ListIndex.get_eq (signals.labels.locate label) ▸ List.get_mem _ _

end SignalMap

end Silean2
