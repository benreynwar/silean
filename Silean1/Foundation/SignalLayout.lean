import Silean.Foundation.SignalSelection
import Silean.Foundation.SignalGroup

namespace Silean

/-!
# Signal layouts

Module interfaces use `SignalMap` because named labels make wiring readable and
type-safe. Hardware structure, however, often needs to traverse an aggregate by
position: a vector has numbered elements and a tuple has ordered fields. This
file connects those two representations without erasing the type of any
component.

There are two main conversions:

* `SignalTypes.get` and `SignalTypes.assemble` convert between a tuple value and
  a dependent function over its field positions.
* `SignalMap.pack` and `SignalMap.unpack` convert between named
  `SignalMap.Values` and the map's canonical positional tuple.

`SignalSelection.valueAt` and `labelAt` relate a positional field back to the
selected parent label. `Composition/SignalAdapter.lean`,
`Modules/NamedTupleAdapter/NamedTupleAdapter.lean`, and
`Modules/TupleField/TupleField.lean` use this machinery to split, combine, and
address aggregate hardware signals.
-/

/-! ## Positional tuple fields -/

inductive SignalTypes.Position : SignalTypes → Type
  | head : Position (.cons head tail)
  | tail : Position tail → Position (.cons head tail)

/- The supporting declarations are private: they exist only to make the
examples compile and cannot be used as library API. -/

@[reducible] private def exampleFields : SignalTypes :=
  .ofList [.bit, .vector 2 .bit]

/-- Positions are type-safe paths into a tuple's field list. These are the only
two positions that can be constructed for `exampleFields`. -/
example : SignalTypes.Position exampleFields := .head

example : SignalTypes.Position exampleFields := .tail .head

private inductive ExampleSignal
  | valid
  | payload
deriving Enumeration

@[reducible] private def exampleSignals : SignalMap :=
  EnumeratedMap.of ExampleSignal fun
    | .valid => .bit
    | .payload => .vector 2 .bit

@[reducible] private def examplePayload : (SignalType.vector 2 .bit).Denote
  | ⟨0, _⟩ => true
  | ⟨1, _⟩ => false

@[reducible] private def exampleValues : exampleSignals.Values
  | .valid => true
  | .payload => examplePayload

@[reducible] private def exampleSelection :
    SignalSelection exampleSignals exampleFields :=
  exampleSignals.selectionFrom [.valid, .payload]

namespace SignalTypes

def Position.ordinal : Position fields → Nat
  | .head => 0
  | .tail position => position.ordinal + 1

def typeAt : (fields : SignalTypes) → Position fields → SignalType
  | .cons head _, .head => head
  | .cons _ tail, .tail position => typeAt tail position

/-- The position determines the result type: the first field is a bit and the
second is a two-bit vector. -/
example : exampleFields.typeAt .head = .bit := rfl

example : exampleFields.typeAt (.tail .head) = .vector 2 .bit := rfl

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

/-- `componentMap` exposes those positions as typed signal labels, which is the
form used by structural tuple splitters. -/
example : exampleFields.componentMap.signalType (.tail .head) =
    .vector 2 .bit := rfl

def get : (fields : SignalTypes) → fields.Denote →
    (position : Position fields) → (typeAt fields position).Denote
  | .cons _ _, (head, _), .head => head
  | .cons _ tail, (_, rest), .tail position => get tail rest position

/-- The same position selects a value whose Lean type is determined by
`typeAt`. -/
example : exampleFields.get (true, (examplePayload, ())) .head = true := rfl

example : exampleFields.get (true, (examplePayload, ())) (.tail .head) 1 = false := rfl

def assemble : (fields : SignalTypes) →
    ((position : Position fields) → (typeAt fields position).Denote) →
      fields.Denote
  | .nil, _ => ()
  | .cons _ tail, values =>
      (values .head, assemble tail fun position => values (.tail position))

example : exampleFields.assemble
    (exampleFields.get (true, (examplePayload, ()))) =
      (true, (examplePayload, ())) := rfl

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

/-! ## Selected signal layouts -/

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

/-- Positional selection fields retrieve the correspondingly typed named
value. -/
example : exampleSelection.valueAt exampleValues (.tail .head) 1 = false := rfl

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

/-- Parent label occupying a positional selection field. This connects
labelled signal maps to positional aggregate adapters. -/
def labelAt : (selection : SignalSelection signals types) →
    SignalTypes.Position types → signals.Label
  | .cons label _, .head => label
  | .cons _ tail, .tail position => tail.labelAt position

/-- The second positional field came from the named `payload` signal. -/
example : exampleSelection.labelAt (.tail .head) = .payload := rfl

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

/-! ## Vector layouts -/

namespace SignalType

@[reducible] def vectorComponents (length : Nat) (element : SignalType) : SignalMap :=
  {
    Key := Fin length
    keys := Enumeration.fin length
    value := fun _ => element }

/-- Vector components are named by their numeric positions. -/
example : (SignalType.vectorComponents 3 .bit).labels.values = [0, 1, 2] := rfl

end SignalType

/-! ## Named tuple layouts -/

namespace SignalMap

/-- The positional tuple field list obtained from a named signal map's
canonical label order. Names remain in the map; only the represented signal
type is positional. -/
@[reducible] def tupleFields (signals : SignalMap) : SignalTypes :=
  .ofList signals.types

example : exampleSignals.tupleFields = exampleFields := rfl

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

example : (exampleSignals.tuplePosition .payload).ordinal = 1 := rfl

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

/-- Packing follows the signal map's canonical label order. -/
example : exampleSignals.pack exampleValues =
    (true, (examplePayload, ())) := rfl

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

example : exampleSignals.unpack (false, (examplePayload, ())) .valid = false := rfl

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
