import Silean2.Foundation.SignalMap

namespace Silean2

/-! Partially specified signal values. Expectations retain the complete signal
shape; `dontCare` exists only at bit leaves. -/

inductive BitExpectation where
  | zero
  | one
  | dontCare
deriving DecidableEq, Repr

namespace BitExpectation

def exact : Bool → BitExpectation
  | false => .zero
  | true => .one

def Matches : BitExpectation → Bool → Prop
  | .zero, value => value = false
  | .one, value => value = true
  | .dontCare, _ => True

@[simp] theorem zero_matches_iff (actual : Bool) :
    BitExpectation.zero.Matches actual ↔ actual = false := Iff.rfl

@[simp] theorem one_matches_iff (actual : Bool) :
    BitExpectation.one.Matches actual ↔ actual = true := Iff.rfl

@[simp] theorem exact_matches_iff (expected actual : Bool) :
    (exact expected).Matches actual ↔ expected = actual := by
  cases expected <;> cases actual <;> simp [exact, Matches]

@[simp] theorem dontCare_matches (actual : Bool) :
    BitExpectation.dontCare.Matches actual := trivial

end BitExpectation

mutual
  def SignalType.Expectation : SignalType → Type
    | .bit => BitExpectation
    | .vector length element => Fin length → element.Expectation
    | .tuple fields => fields.Expectation

  def SignalTypes.Expectation : SignalTypes → Type
    | .nil => Unit
    | .cons head tail => head.Expectation × tail.Expectation
end

mutual
  def SignalType.exactExpectation : (signalType : SignalType) →
      signalType.Denote → signalType.Expectation
    | .bit, value => BitExpectation.exact value
    | .vector _ element, value =>
        fun index => element.exactExpectation (value index)
    | .tuple fields, value => fields.exactExpectation value

  def SignalTypes.exactExpectation : (signalTypes : SignalTypes) →
      signalTypes.Denote → signalTypes.Expectation
    | .nil, () => ()
    | .cons head tail, (headValue, tailValue) =>
        (head.exactExpectation headValue, tail.exactExpectation tailValue)
end

mutual
  def SignalType.dontCareExpectation : (signalType : SignalType) →
      signalType.Expectation
    | .bit => .dontCare
    | .vector _ element => fun _ => element.dontCareExpectation
    | .tuple fields => fields.dontCareExpectation

  def SignalTypes.dontCareExpectation : (signalTypes : SignalTypes) →
      signalTypes.Expectation
    | .nil => ()
    | .cons head tail =>
        (head.dontCareExpectation, tail.dontCareExpectation)
end

mutual
  def SignalType.Matches : (signalType : SignalType) →
      signalType.Expectation → signalType.Denote → Prop
    | .bit, expectation, value => expectation.Matches value
    | .vector _ element, expectation, value =>
        ∀ index, element.Matches (expectation index) (value index)
    | .tuple fields, expectation, value => fields.Matches expectation value

  def SignalTypes.Matches : (signalTypes : SignalTypes) →
      signalTypes.Expectation → signalTypes.Denote → Prop
    | .nil, (), () => True
    | .cons head tail, (headExpectation, tailExpectation),
        (headValue, tailValue) =>
      head.Matches headExpectation headValue ∧
        tail.Matches tailExpectation tailValue
end

namespace SignalType

@[simp] theorem vector_matches_iff (element : SignalType)
    (expectation : (SignalType.vector length element).Expectation)
    (value : (SignalType.vector length element).Denote) :
    (SignalType.vector length element).Matches expectation value ↔
      ∀ index, element.Matches (expectation index) (value index) := Iff.rfl

end SignalType

namespace SignalTypes

@[simp] theorem nil_matches :
    SignalTypes.nil.Matches () () := trivial

@[simp] theorem cons_matches_iff (head : SignalType) (tail : SignalTypes)
    (headExpectation : head.Expectation)
    (tailExpectation : tail.Expectation)
    (headValue : head.Denote) (tailValue : tail.Denote) :
    (SignalTypes.cons head tail).Matches
        (headExpectation, tailExpectation) (headValue, tailValue) ↔
      head.Matches headExpectation headValue ∧
        tail.Matches tailExpectation tailValue := Iff.rfl

end SignalTypes

mutual
  @[simp] theorem SignalType.exactExpectation_matches_iff :
      ∀ (signalType : SignalType) (expected actual : signalType.Denote),
        signalType.Matches (signalType.exactExpectation expected) actual ↔
          expected = actual
    | .bit, expected, actual => BitExpectation.exact_matches_iff expected actual
    | .vector length element, expected, actual => by
        change (∀ index, element.Matches
          (element.exactExpectation (expected index)) (actual index)) ↔ _
        simp only [SignalType.exactExpectation_matches_iff]
        constructor
        · intro pointwise
          funext index
          exact pointwise index
        · intro equal
          cases equal
          exact fun _ => rfl
    | .tuple fields, expected, actual =>
        SignalTypes.exactExpectation_matches_iff fields expected actual

  @[simp] theorem SignalTypes.exactExpectation_matches_iff :
      ∀ (signalTypes : SignalTypes)
        (expected actual : signalTypes.Denote),
        signalTypes.Matches (signalTypes.exactExpectation expected) actual ↔
          expected = actual
    | .nil, (), () => by
        constructor
        · intro _
          rfl
        · intro _
          trivial
    | .cons head tail, (expectedHead, expectedTail),
        (actualHead, actualTail) => by
      change (head.Matches (head.exactExpectation expectedHead) actualHead ∧
          tail.Matches (tail.exactExpectation expectedTail) actualTail) ↔ _
      rw [SignalType.exactExpectation_matches_iff,
        SignalTypes.exactExpectation_matches_iff tail]
      constructor
      · rintro ⟨rfl, rfl⟩
        rfl
      · intro equal
        cases equal
        exact ⟨rfl, rfl⟩
end

mutual
  @[simp] theorem SignalType.dontCareExpectation_matches :
      ∀ (signalType : SignalType) (actual : signalType.Denote),
        signalType.Matches signalType.dontCareExpectation actual
    | .bit, actual => BitExpectation.dontCare_matches actual
    | .vector _ element, actual =>
        fun index => element.dontCareExpectation_matches (actual index)
    | .tuple fields, actual => fields.dontCareExpectation_matches actual

  @[simp] theorem SignalTypes.dontCareExpectation_matches :
      ∀ (signalTypes : SignalTypes) (actual : signalTypes.Denote),
        signalTypes.Matches signalTypes.dontCareExpectation actual
    | .nil, () => trivial
    | .cons head tail, (headValue, tailValue) =>
        ⟨head.dontCareExpectation_matches headValue,
          tail.dontCareExpectation_matches tailValue⟩
end

namespace SignalMap

abbrev Expectations (signalMap : SignalMap) :=
  (label : signalMap.Label) → (signalMap.signalType label).Expectation

def exactExpectations (signalMap : SignalMap) (values : signalMap.Values) :
    signalMap.Expectations :=
  fun label => (signalMap.signalType label).exactExpectation (values label)

def dontCareExpectations (signalMap : SignalMap) : signalMap.Expectations :=
  fun label => (signalMap.signalType label).dontCareExpectation

def Matches (signalMap : SignalMap) (expectations : signalMap.Expectations)
    (values : signalMap.Values) : Prop :=
  ∀ label, (signalMap.signalType label).Matches
    (expectations label) (values label)

@[simp] theorem exactExpectations_match_iff (signalMap : SignalMap)
    (expected actual : signalMap.Values) :
    signalMap.Matches (signalMap.exactExpectations expected) actual ↔
      expected = actual := by
  constructor
  · intro pointwise
    funext label
    exact ((signalMap.signalType label).exactExpectation_matches_iff
      (expected label) (actual label)).mp (pointwise label)
  · intro equal
    cases equal
    intro label
    exact ((signalMap.signalType label).exactExpectation_matches_iff
      (expected label) (expected label)).mpr rfl

@[simp] theorem dontCareExpectations_match (signalMap : SignalMap)
    (actual : signalMap.Values) :
    signalMap.Matches signalMap.dontCareExpectations actual :=
  fun label => (signalMap.signalType label).dontCareExpectation_matches
    (actual label)

end SignalMap

end Silean2
