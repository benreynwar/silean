import Silean.Composition.SignalAdapterImplementation
import Silean.Primitives.Xor

namespace Silean

open Composition

/-! Boolean operations lifted structurally through vectors and tuples.  These
functions describe contract behavior; physical modules still recurse to
single-bit primitive leaves. -/

def allFin : (width : Nat) → (Fin width → Bool) → Bool
  | 0, _ => true
  | width + 1, values => values 0 && allFin width (fun index => values index.succ)

theorem allFin_eq_true_iff : ∀ (width : Nat) (values : Fin width → Bool),
    allFin width values = true ↔ ∀ index, values index = true
  | 0, _ => by
      constructor
      · intro _ index; exact Fin.elim0 index
      · intro _; rfl
  | width + 1, values => by
      simp only [allFin, Bool.and_eq_true, allFin_eq_true_iff]
      constructor
      · rintro ⟨head, tail⟩ index
        exact Fin.cases head tail index
      · intro every
        exact ⟨every 0, fun index => every index.succ⟩

mutual
  def SignalType.equal : (signalType : SignalType) →
      signalType.Denote → signalType.Denote → Bool
    | .bit, left, right => (left && right) || (!left && !right)
    | .vector length element, left, right =>
        allFin length fun index => element.equal (left index) (right index)
    | .tuple fields, left, right => fields.equal left right

  def SignalTypes.equal : (fields : SignalTypes) →
      fields.Denote → fields.Denote → Bool
    | .nil, (), () => true
    | .cons head tail, (leftHead, leftTail), (rightHead, rightTail) =>
        head.equal leftHead rightHead && tail.equal leftTail rightTail
end

mutual
  theorem SignalType.equal_eq_true_iff : ∀ (signalType : SignalType)
      (left right : signalType.Denote),
      signalType.equal left right = true ↔ left = right
    | .bit, left, right => by cases left <;> cases right <;> simp [SignalType.equal]
    | .vector length element, left, right => by
        rw [show SignalType.equal (.vector length element) left right =
            allFin length (fun index => element.equal (left index) (right index)) by rfl]
        rw [allFin_eq_true_iff]
        constructor
        · intro pointwise
          funext index
          exact (SignalType.equal_eq_true_iff element _ _).mp (pointwise index)
        · intro equal
          subst right
          intro index
          exact (SignalType.equal_eq_true_iff element _ _).mpr rfl
    | .tuple fields, left, right => by
        change fields.equal left right = true ↔ left = right
        exact SignalTypes.equal_eq_true_iff fields left right

  theorem SignalTypes.equal_eq_true_iff : ∀ (fields : SignalTypes)
      (left right : fields.Denote),
      fields.equal left right = true ↔ left = right
    | .nil, (), () => by simp [SignalTypes.equal]
    | .cons head tail, (leftHead, leftTail), (rightHead, rightTail) => by
        simp only [SignalTypes.equal, Bool.and_eq_true,
          SignalType.equal_eq_true_iff head,
          SignalTypes.equal_eq_true_iff tail]
        constructor
        · rintro ⟨rfl, rfl⟩; rfl
        · intro equal
          cases equal
          exact ⟨rfl, rfl⟩
end

mutual
  def SignalType.mask : (signalType : SignalType) →
      signalType.Denote → Bool → signalType.Denote
    | .bit, value, mask => value && mask
    | .vector _ element, value, mask =>
        fun index => element.mask (value index) mask
    | .tuple fields, value, mask => fields.mask value mask

  def SignalTypes.mask : (fields : SignalTypes) →
      fields.Denote → Bool → fields.Denote
    | .nil, (), _ => ()
    | .cons head tail, (headValue, tailValue), mask =>
        (head.mask headValue mask, tail.mask tailValue mask)
end

mutual
  def SignalType.bitwiseOr : (signalType : SignalType) →
      signalType.Denote → signalType.Denote → signalType.Denote
    | .bit, left, right => left || right
    | .vector _ element, left, right =>
        fun index => element.bitwiseOr (left index) (right index)
    | .tuple fields, left, right => fields.bitwiseOr left right

  def SignalTypes.bitwiseOr : (fields : SignalTypes) →
      fields.Denote → fields.Denote → fields.Denote
    | .nil, (), () => ()
    | .cons head tail, (leftHead, leftTail), (rightHead, rightTail) =>
        (head.bitwiseOr leftHead rightHead, tail.bitwiseOr leftTail rightTail)
end

mutual
  def SignalType.bitwiseAnd : (signalType : SignalType) →
      signalType.Denote → signalType.Denote → signalType.Denote
    | .bit, left, right => left && right
    | .vector _ element, left, right =>
        fun index => element.bitwiseAnd (left index) (right index)
    | .tuple fields, left, right => fields.bitwiseAnd left right

  def SignalTypes.bitwiseAnd : (fields : SignalTypes) →
      fields.Denote → fields.Denote → fields.Denote
    | .nil, (), () => ()
    | .cons head tail, (leftHead, leftTail), (rightHead, rightTail) =>
        (head.bitwiseAnd leftHead rightHead, tail.bitwiseAnd leftTail rightTail)
end

mutual
  def SignalType.bitwiseXor : (signalType : SignalType) →
      signalType.Denote → signalType.Denote → signalType.Denote
    | .bit, left, right => Primitives.xorValue left right
    | .vector _ element, left, right =>
        fun index => element.bitwiseXor (left index) (right index)
    | .tuple fields, left, right => fields.bitwiseXor left right

  def SignalTypes.bitwiseXor : (fields : SignalTypes) →
      fields.Denote → fields.Denote → fields.Denote
    | .nil, (), () => ()
    | .cons head tail, (leftHead, leftTail), (rightHead, rightTail) =>
        (head.bitwiseXor leftHead rightHead, tail.bitwiseXor leftTail rightTail)
end

namespace SignalTypes

theorem get_mask : ∀ (fields : SignalTypes) (value : fields.Denote)
    (mask : Bool) (position : Position fields),
    get fields (fields.mask value mask) position =
      (typeAt fields position).mask (get fields value position) mask
  | .cons _ _, (_, _), _, .head => rfl
  | .cons _ tail, (_, tailValue), mask, .tail position =>
      get_mask tail tailValue mask position

theorem get_bitwiseOr : ∀ (fields : SignalTypes)
    (left right : fields.Denote) (position : Position fields),
    get fields (fields.bitwiseOr left right) position =
      (typeAt fields position).bitwiseOr
        (get fields left position) (get fields right position)
  | .cons _ _, (_, _), (_, _), .head => rfl
  | .cons _ tail, (_, leftTail), (_, rightTail), .tail position =>
      get_bitwiseOr tail leftTail rightTail position

theorem get_bitwiseAnd : ∀ (fields : SignalTypes)
    (left right : fields.Denote) (position : Position fields),
    get fields (fields.bitwiseAnd left right) position =
      (typeAt fields position).bitwiseAnd
        (get fields left position) (get fields right position)
  | .cons _ _, (_, _), (_, _), .head => rfl
  | .cons _ tail, (_, leftTail), (_, rightTail), .tail position =>
      get_bitwiseAnd tail leftTail rightTail position

theorem get_bitwiseXor : ∀ (fields : SignalTypes)
    (left right : fields.Denote) (position : Position fields),
    get fields (fields.bitwiseXor left right) position =
      (typeAt fields position).bitwiseXor
        (get fields left position) (get fields right position)
  | .cons _ _, (_, _), (_, _), .head => rfl
  | .cons _ tail, (_, leftTail), (_, rightTail), .tail position =>
      get_bitwiseXor tail leftTail rightTail position

end SignalTypes

namespace SignalSelection

theorem project_mask (selection : SignalSelection signals types)
    (values : signals.Values) (mask : Bool) :
    selection.project (fun label =>
      (signals.signalType label).mask (values label) mask) =
      types.mask (selection.project values) mask := by
  induction selection with
  | nil => rfl
  | cons label tail induction =>
      change (_, _) = (_, _)
      rw [induction]

theorem project_bitwiseOr (selection : SignalSelection signals types)
    (left right : signals.Values) :
    selection.project (fun label =>
      (signals.signalType label).bitwiseOr (left label) (right label)) =
      types.bitwiseOr (selection.project left) (selection.project right) := by
  induction selection with
  | nil => rfl
  | cons label tail induction =>
      change (_, _) = (_, _)
      rw [induction]

theorem project_bitwiseAnd (selection : SignalSelection signals types)
    (left right : signals.Values) :
    selection.project (fun label =>
      (signals.signalType label).bitwiseAnd (left label) (right label)) =
      types.bitwiseAnd (selection.project left) (selection.project right) := by
  induction selection with
  | nil => rfl
  | cons label tail induction =>
      change (_, _) = (_, _)
      rw [induction]

theorem project_bitwiseXor (selection : SignalSelection signals types)
    (left right : signals.Values) :
    selection.project (fun label =>
      (signals.signalType label).bitwiseXor (left label) (right label)) =
      types.bitwiseXor (selection.project left) (selection.project right) := by
  induction selection with
  | nil => rfl
  | cons label tail induction =>
      change (_, _) = (_, _)
      rw [induction]

end SignalSelection

namespace SignalMap

theorem pack_mask (signals : SignalMap.{0}) (values : signals.Values)
    (mask : Bool) :
    signals.pack (fun field =>
      (signals.signalType field).mask (values field) mask) =
      signals.tupleType.mask (signals.pack values) mask := by
  change signals.allSelection.project _ =
    signals.tupleFields.mask (signals.allSelection.project values) mask
  exact signals.allSelection.project_mask values mask

theorem pack_bitwiseOr (signals : SignalMap.{0})
    (left right : signals.Values) :
    signals.pack (fun field =>
      (signals.signalType field).bitwiseOr (left field) (right field)) =
      signals.tupleType.bitwiseOr (signals.pack left) (signals.pack right) := by
  change signals.allSelection.project _ = signals.tupleFields.bitwiseOr
    (signals.allSelection.project left) (signals.allSelection.project right)
  exact signals.allSelection.project_bitwiseOr left right

theorem pack_bitwiseAnd (signals : SignalMap.{0})
    (left right : signals.Values) :
    signals.pack (fun field =>
      (signals.signalType field).bitwiseAnd (left field) (right field)) =
      signals.tupleType.bitwiseAnd (signals.pack left) (signals.pack right) := by
  change signals.allSelection.project _ = signals.tupleFields.bitwiseAnd
    (signals.allSelection.project left) (signals.allSelection.project right)
  exact signals.allSelection.project_bitwiseAnd left right

theorem pack_bitwiseXor (signals : SignalMap.{0})
    (left right : signals.Values) :
    signals.pack (fun field =>
      (signals.signalType field).bitwiseXor (left field) (right field)) =
      signals.tupleType.bitwiseXor (signals.pack left) (signals.pack right) := by
  change signals.allSelection.project _ = signals.tupleFields.bitwiseXor
    (signals.allSelection.project left) (signals.allSelection.project right)
  exact signals.allSelection.project_bitwiseXor left right

theorem unpack_mask (signals : SignalMap.{0}) (value : signals.tupleType.Denote)
    (mask : Bool) :
    signals.unpack (signals.tupleType.mask value mask) =
      fun field => (signals.signalType field).mask (signals.unpack value field) mask := by
  apply signals.pack_injective
  rw [signals.pack_unpack, signals.pack_mask, signals.pack_unpack]

theorem unpack_bitwiseOr (signals : SignalMap.{0})
    (left right : signals.tupleType.Denote) :
    signals.unpack (signals.tupleType.bitwiseOr left right) =
      fun field => (signals.signalType field).bitwiseOr
        (signals.unpack left field) (signals.unpack right field) := by
  apply signals.pack_injective
  rw [signals.pack_unpack, signals.pack_bitwiseOr,
    signals.pack_unpack, signals.pack_unpack]

theorem unpack_bitwiseAnd (signals : SignalMap.{0})
    (left right : signals.tupleType.Denote) :
    signals.unpack (signals.tupleType.bitwiseAnd left right) =
      fun field => (signals.signalType field).bitwiseAnd
        (signals.unpack left field) (signals.unpack right field) := by
  apply signals.pack_injective
  rw [signals.pack_unpack, signals.pack_bitwiseAnd,
    signals.pack_unpack, signals.pack_unpack]

theorem unpack_bitwiseXor (signals : SignalMap.{0})
    (left right : signals.tupleType.Denote) :
    signals.unpack (signals.tupleType.bitwiseXor left right) =
      fun field => (signals.signalType field).bitwiseXor
        (signals.unpack left field) (signals.unpack right field) := by
  apply signals.pack_injective
  rw [signals.pack_unpack, signals.pack_bitwiseXor,
    signals.pack_unpack, signals.pack_unpack]

end SignalMap

namespace SignalSplitter

theorem split_mask (splitter : SignalSplitter)
    (value : splitter.aggregateType.Denote) (mask : Bool) :
    splitter.outputValues
        (splitter.inputValues (splitter.aggregateType.mask value mask)) =
      fun component =>
        (splitter.ports.outputs.signalType component).mask
          (splitter.outputValues (splitter.inputValues value) component) mask := by
  cases splitter with
  | vector => rfl
  | tuple fields => funext component; exact fields.get_mask value mask component

theorem split_bitwiseOr (splitter : SignalSplitter)
    (left right : splitter.aggregateType.Denote) :
    splitter.outputValues
        (splitter.inputValues (splitter.aggregateType.bitwiseOr left right)) =
      fun component =>
        (splitter.ports.outputs.signalType component).bitwiseOr
          (splitter.outputValues (splitter.inputValues left) component)
          (splitter.outputValues (splitter.inputValues right) component) := by
  cases splitter with
  | vector => rfl
  | tuple fields => funext component; exact fields.get_bitwiseOr left right component

theorem split_bitwiseAnd (splitter : SignalSplitter)
    (left right : splitter.aggregateType.Denote) :
    splitter.outputValues
        (splitter.inputValues (splitter.aggregateType.bitwiseAnd left right)) =
      fun component =>
        (splitter.ports.outputs.signalType component).bitwiseAnd
          (splitter.outputValues (splitter.inputValues left) component)
          (splitter.outputValues (splitter.inputValues right) component) := by
  cases splitter with
  | vector => rfl
  | tuple fields => funext component; exact fields.get_bitwiseAnd left right component

theorem split_bitwiseXor (splitter : SignalSplitter)
    (left right : splitter.aggregateType.Denote) :
    splitter.outputValues
        (splitter.inputValues (splitter.aggregateType.bitwiseXor left right)) =
      fun component =>
        (splitter.ports.outputs.signalType component).bitwiseXor
          (splitter.outputValues (splitter.inputValues left) component)
          (splitter.outputValues (splitter.inputValues right) component) := by
  cases splitter with
  | vector => rfl
  | tuple fields => funext component; exact fields.get_bitwiseXor left right component

end SignalSplitter

end Silean
