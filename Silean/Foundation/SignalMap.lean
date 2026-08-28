import Silean.Foundation.SignalType
import Silean.Foundation.Enumeration

namespace Silean

/-! Labelled, canonically ordered collections of typed signals. -/

abbrev SignalMap := EnumeratedMap SignalType

abbrev SignalMap.Label (signalMap : SignalMap) := signalMap.Key
abbrev SignalMap.labels (signalMap : SignalMap) := signalMap.keys
abbrev SignalMap.signalType (signalMap : SignalMap) := signalMap.value

def SignalMap.types (signalMap : SignalMap) : List SignalType :=
  signalMap.orderedValues

def SignalMap.tupleType (signalMap : SignalMap) : SignalType :=
  .tupleOfList signalMap.types

abbrev SignalMap.Values (signalMap : SignalMap) :=
  (label : signalMap.Label) → (signalMap.signalType label).Denote

def SignalMap.defaultValues (signalMap : SignalMap) : signalMap.Values :=
  fun label => (signalMap.signalType label).default

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

instance : Enumeration NoSignal :=
  Enumeration.empty fun signal => nomatch signal

def emptySignalMap : SignalMap :=
  EnumeratedMap.of NoSignal fun signal => nomatch signal

def SignalMap.emptyValues : emptySignalMap.Values :=
  fun signal => nomatch signal

end Silean
