import Silean.Foundation.SignalSelection
import Silean.Foundation.SignalGroup

namespace Silean

/-! Shared machinery for viewing vectors and tuples as their immediate
components.  The public structural components that use this machinery are
closed to those two aggregate forms. -/

inductive SignalTypes.Position : SignalTypes → Type
  | head : Position (.cons head tail)
  | tail : Position tail → Position (.cons head tail)

namespace SignalTypes

def Position.ordinal : Position fields → Nat
  | .head => 0
  | .tail position => position.ordinal + 1

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

@[reducible] def componentMap (fields : SignalTypes) : SignalMap where
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

theorem get_injective (fields : SignalTypes) : Function.Injective fields.get := by
  intro left right equal
  simpa only [assemble_get] using congrArg fields.assemble equal

@[simp] theorem get_inj (fields : SignalTypes) (left right : fields.Denote) :
    fields.get left = fields.get right ↔ left = right :=
  fields.get_injective.eq_iff

end SignalTypes

namespace SignalSelection

/-- Retrieve a label-indexed dependent value at a positional selection field.
This is the computational bridge from named maps to tuple component ports. -/
def valueAt (selection : SignalSelection signals types)
    {motive : SignalType → Type u}
    (values : (label : signals.Label) → motive (signals.signalType label)) :
    (position : SignalTypes.Position types) → motive (types.typeAt position)
  := fun position => match selection, position with
    | .cons label _, .head => values label
    | .cons _ tail, .tail position => tail.valueAt values position

theorem valueAt_map (selection : SignalSelection signals types)
    {source : SignalType → Type u} {target : SignalType → Type v}
    (values : (label : signals.Label) → source (signals.signalType label))
    (map : (signalType : SignalType) → source signalType → target signalType)
    (position : SignalTypes.Position types) :
    selection.valueAt (fun label => map _ (values label)) position =
      map _ (selection.valueAt values position) := by
  induction selection with
  | nil => exact nomatch position
  | cons label tail induction =>
      cases position with
      | head => rfl
      | tail position => exact induction position

theorem assemble_valueAt (selection : SignalSelection signals types)
    (values : signals.Values) :
    types.assemble (selection.valueAt values) = selection.project values := by
  induction selection with
  | nil => rfl
  | cons label tail induction =>
      apply Prod.ext
      · rfl
      · exact induction

@[simp] theorem get_project (selection : SignalSelection signals types)
    (values : signals.Values) (position : SignalTypes.Position types) :
    types.get (selection.project values) position = selection.valueAt values position := by
  induction selection with
  | nil => exact nomatch position
  | cons label tail induction =>
      cases position with
      | head => rfl
      | tail position => exact induction position

/-- Parent label occupying a positional selection field. This supports the
temporary migration of rules whose targets are still naturally positional. -/
def labelAt : (selection : SignalSelection signals types) →
    SignalTypes.Position types → signals.Label
  | .cons label _, .head => label
  | .cons _ tail, .tail position => tail.labelAt position

@[simp] theorem signalType_labelAt :
    (selection : SignalSelection signals types) →
    (position : SignalTypes.Position types) →
    SignalTypes.typeAt types position =
      signals.signalType (selection.labelAt position)
  | .cons _ _, .head => rfl
  | .cons _ tail, .tail position => tail.signalType_labelAt position

theorem cast_labelAt_value (selection : SignalSelection signals types)
    (values : signals.Values) (position : SignalTypes.Position types) :
    (selection.signalType_labelAt position).symm ▸
        values (selection.labelAt position) =
      selection.valueAt values position := by
  induction selection with
  | nil => exact nomatch position
  | cons label tail induction =>
      cases position with
      | head => rfl
      | tail position => exact induction position

/-- Updating a parent signal outside a selection does not change the selected
values. -/
theorem project_set_of_not_mem (selection : SignalSelection signals types)
    (values : signals.Values) (label : signals.Label)
    (value : (signals.signalType label).Denote)
    (notMember : label ∉ selection.labels) :
    selection.project (signals.set values label value) = selection.project values := by
  induction selection with
  | nil => rfl
  | cons selected tail induction =>
      simp only [SignalSelection.labels, List.mem_cons, not_or] at notMember
      simp only [SignalSelection.project]
      rw [SignalMap.set_other _ _ _ _ (Ne.symm notMember.1), induction notMember.2]

end SignalSelection

namespace SignalType

@[reducible] def vectorComponents (length : Nat) (element : SignalType) : SignalMap :=
  {
    Key := Fin length
    keys := Enumeration.fin length
    value := fun _ => element }

end SignalType

namespace SignalMap

/-- The positional tuple field list obtained from a named signal map's
canonical label order. Names remain in the map; only the represented signal
type is positional. -/
@[reducible] def tupleFields (signals : SignalMap) : SignalTypes :=
  .ofList signals.types

private def positionOfIndex (signals : SignalMap) :
    {labels : List signals.Label} → {label : signals.Label} →
      ListIndex label labels →
        SignalTypes.Position (.ofList (labels.map signals.signalType))
  | _ :: _, _, .head => .head
  | _ :: _, _, .tail index => .tail (signals.positionOfIndex index)

/-- The tuple position occupied by a named signal in canonical label order. -/
def tuplePosition (signals : SignalMap) (label : signals.Label) :
    SignalTypes.Position signals.tupleFields :=
  signals.positionOfIndex (signals.labels.locate label)

private theorem typeAt_positionOfIndex (signals : SignalMap) :
    {labels : List signals.Label} → {label : signals.Label} →
      (index : ListIndex label labels) →
        SignalTypes.typeAt (.ofList (labels.map signals.signalType))
          (signals.positionOfIndex index) = signals.signalType label
  | _ :: _, _, .head => rfl
  | _ :: _, _, .tail index => signals.typeAt_positionOfIndex index

theorem typeAt_tuplePosition (signals : SignalMap) (label : signals.Label) :
    SignalTypes.typeAt signals.tupleFields (signals.tuplePosition label) =
      signals.signalType label :=
  signals.typeAt_positionOfIndex (signals.labels.locate label)

def selectionFrom (signals : SignalMap) :
    (labels : List signals.Label) →
      SignalSelection signals (.ofList (labels.map signals.signalType))
  | [] => .nil
  | label :: rest => .cons label (selectionFrom signals rest)

def allSelection (signals : SignalMap) :
    SignalSelection signals signals.tupleFields :=
  selectionFrom signals signals.labels.values

private theorem cast_valueAt_positionOfIndex (signals : SignalMap) :
    {labels : List signals.Label} → {label : signals.Label} →
      (index : ListIndex label labels) → (values : signals.Values) →
      (signals.typeAt_positionOfIndex index) ▸
          (signals.selectionFrom labels).valueAt values
            (signals.positionOfIndex index) =
        values label
  | _ :: _, _, .head, _ => rfl
  | _ :: _, _, .tail index, values =>
      signals.cast_valueAt_positionOfIndex index values

theorem cast_valueAt_tuplePosition (signals : SignalMap)
    (values : signals.Values) (label : signals.Label) :
    signals.typeAt_tuplePosition label ▸
        signals.allSelection.valueAt values (signals.tuplePosition label) =
      values label :=
  signals.cast_valueAt_positionOfIndex (signals.labels.locate label) values

/-- Pack named values into their tuple representation, in canonical label
order. Hardware tuple combiners implement this function. -/
def pack (signals : SignalMap) (values : signals.Values) :
    signals.tupleType.Denote :=
  signals.allSelection.project values

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
    signals.tupleType.Denote → signals.Values :=
  unpackFrom signals signals.labels.values

private theorem project_unpackFrom (signals : SignalMap) :
    ∀ (labels : List signals.Label) (_nodup : labels.Nodup)
      (value : (SignalTypes.ofList (labels.map signals.signalType)).Denote),
      (signals.selectionFrom labels).project
        (signals.unpackFrom labels value) = value
  | [], _, value => by cases value; rfl
  | head :: tail, nodup, value => by
      rcases value with ⟨headValue, tailValue⟩
      have parts := List.nodup_cons.mp nodup
      change
        (signals.set (signals.unpackFrom tail tailValue) head headValue head,
          (signals.selectionFrom tail).project
            (signals.set (signals.unpackFrom tail tailValue) head headValue)) =
          (headValue, tailValue)
      apply Prod.ext
      · exact SignalMap.set_same _ _ _
      · rw [SignalSelection.project_set_of_not_mem]
        · exact signals.project_unpackFrom tail parts.2 tailValue
        · simpa using parts.1

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

/-- Unpacking values packed from a named map recovers the original values. -/
@[simp] theorem unpack_pack (signals : SignalMap) (values : signals.Values) :
    signals.unpack (signals.pack values) = values :=
  signals.unpack_project values

theorem pack_injective (signals : SignalMap) : Function.Injective signals.pack := by
  intro left right equal
  rw [← signals.unpack_pack left, ← signals.unpack_pack right, equal]

/-- Packing an unpacked tuple preserves the tuple exactly. -/
@[simp] theorem pack_unpack (signals : SignalMap)
    (value : signals.tupleType.Denote) :
    signals.pack (signals.unpack value) = value := by
  exact signals.project_unpackFrom signals.labels.values
    signals.labels.nodup value

end SignalMap

end Silean
