import Silean.Foundation.SignalType
import Silean.Foundation.DeriveEnumeration

namespace Silean

/-! Labelled, canonically ordered collections of typed signals. -/

/-- A finite collection of signals addressed by readable, typed labels rather
than positions. This lets module interfaces, contracts, and wiring refer to
signals by meaningful names while Lean checks the type of each referenced
signal. The underlying enumeration provides an order for structural traversal
and emission. -/
abbrev SignalMap := EnumeratedMap SignalType

abbrev SignalMap.Label (signalMap : SignalMap) := signalMap.Key
abbrev SignalMap.labels (signalMap : SignalMap) := signalMap.keys
abbrev SignalMap.signalType (signalMap : SignalMap) := signalMap.value

/- The supporting declarations are private: they exist only to make the
examples compile and cannot be used as library API. -/

private inductive ExampleSignal
  | valid
  | payload
deriving Enumeration

@[reducible] private def exampleSignals : SignalMap :=
  EnumeratedMap.of ExampleSignal fun
    | .valid => .bit
    | .payload => .vector 8 .bit

/-- A signal map gives each label its own signal type while retaining a stable
order for traversal. -/
example : exampleSignals.labels.values = [.valid, .payload] := rfl

example : exampleSignals.signalType .payload = .vector 8 .bit := rfl

def SignalMap.types (signalMap : SignalMap) : List SignalType :=
  signalMap.orderedValues

example : exampleSignals.types = [.bit, .vector 8 .bit] := rfl

def SignalMap.tupleType (signalMap : SignalMap) : SignalType :=
  .tupleOfList signalMap.types

example : exampleSignals.tupleType =
    .tuple (.cons .bit (.cons (.vector 8 .bit) .nil)) := rfl

abbrev SignalMap.Values (signalMap : SignalMap) :=
  (label : signalMap.Label) → (signalMap.signalType label).Denote

/-- A valuation is dependently typed: `valid` contains a `Bool`, while
`payload` contains eight `Bool` values. -/
private def exampleValues : exampleSignals.Values
  | .valid => true
  | .payload => fun _ => true

example : exampleValues .valid = true := rfl

example : exampleValues .payload 0 = true := rfl

def SignalMap.defaultValues (signalMap : SignalMap) : signalMap.Values :=
  fun label => (signalMap.signalType label).default

example : exampleSignals.defaultValues .valid = false := rfl

example : exampleSignals.defaultValues .payload 0 = false := rfl

def SignalMap.set (signalMap : SignalMap) (values : signalMap.Values)
    (label : signalMap.Label) (value : (signalMap.signalType label).Denote) :
    signalMap.Values := by
  letI : DecidableEq signalMap.Label := signalMap.labels.decidableEq
  intro other
  if equal : other = label then
    cases equal
    exact value
  else
    exact values other

/-- Updating one label preserves values stored at the other labels. -/
example : exampleSignals.set exampleValues .valid false .valid = false := rfl

example : exampleSignals.set exampleValues .valid false .payload 0 = true := rfl

@[simp] theorem SignalMap.set_same
    {signalMap : SignalMap} (values : signalMap.Values) (label : signalMap.Label)
    (value : (signalMap.signalType label).Denote) :
    SignalMap.set signalMap values label value label = value := by
  simp [set]

theorem SignalMap.set_other
    {signalMap : SignalMap} (values : signalMap.Values)
    (label other : signalMap.Label)
    (value : (signalMap.signalType label).Denote) (different : other ≠ label) :
    SignalMap.set signalMap values label value other = values other := by
  simp [set, different]

inductive NoSignal

@[reducible] instance : Enumeration NoSignal :=
  Enumeration.empty fun signal => nomatch signal

@[enumeration] theorem noSignalEnumerationValues :
    (inferInstance : Enumeration NoSignal).values = [] := rfl

def emptySignalMap : SignalMap :=
  EnumeratedMap.of NoSignal fun signal => nomatch signal

def SignalMap.emptyValues : emptySignalMap.Values :=
  fun signal => nomatch signal

example : emptySignalMap.types = [] := rfl

example : emptySignalMap.tupleType = .tuple .nil := rfl

instance : Subsingleton emptySignalMap.Values where
  allEq left right := by
    funext signal
    exact nomatch signal

end Silean
