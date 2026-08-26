import Silean2.SignalAdapterCertified

namespace Silean2

/-! Boolean operations lifted structurally through vectors and tuples.  These
functions describe contract behavior; physical modules still recurse to
single-bit primitive leaves. -/

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

end Silean2
