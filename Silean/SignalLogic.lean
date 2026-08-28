import Silean.SignalAdapterCertified

namespace Silean

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

end SignalTypes

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
  | tuple fields =>
      funext component
      exact fields.get_mask value mask component

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
  | tuple fields =>
      funext component
      exact fields.get_bitwiseOr left right component

end SignalSplitter

end Silean
