import Silean.Foundation.SignalMap

namespace Silean

/-!
# Signal selections

A `SignalMap.Values` contains a value for every named signal in a map. Consumers
often need only some of those signals, arranged as a positional tuple in a
specific order. A plain list of labels identifies that subset, but its type does
not say what type of tuple will result. `SignalSelection signals types` couples
the labels to their ordered `SignalTypes`, allowing `project` to return
`types.Denote` without runtime type checks or optional values.

For example, selecting a bit-valued `valid` label followed by an eight-bit
`payload` label produces a value of the tuple type described by
`.ofList [.bit, .vector 8 .bit]`. Selection order is significant and may differ
from the `SignalMap`'s canonical enumeration order.
-/

inductive SignalSelection (signals : SignalMap) : SignalTypes → Type
  | nil : SignalSelection signals .nil
  | cons (label : signals.Label) (tail : SignalSelection signals types) :
      SignalSelection signals (.cons (signals.signalType label) types)

/-- Select an ordered list of labels. The selection's type records the signal
type belonging to each label in the same order. -/
def SignalMap.selectionFrom (signals : SignalMap) :
    (labels : List signals.Label) →
      SignalSelection signals (.ofList (labels.map signals.signalType))
  | [] => .nil
  | label :: rest => .cons label (selectionFrom signals rest)

/- The supporting declarations are private: they exist only to make the
examples compile and cannot be used as library API. -/

private inductive ExampleSignal
  | valid
  | ready
  | payload
deriving Enumeration

@[reducible] private def exampleSignals : SignalMap :=
  EnumeratedMap.of ExampleSignal fun
    | .valid => .bit
    | .ready => .bit
    | .payload => .vector 8 .bit

example : SignalSelection exampleSignals .nil := .nil

example : SignalSelection exampleSignals
    (.ofList [.bit, .vector 8 .bit]) :=
  exampleSignals.selectionFrom [.valid, .payload]

namespace SignalSelection

def prepend (tail : SignalSelection signals types) (label : signals.Label) :
    SignalSelection signals (.cons (signals.signalType label) types) :=
  .cons label tail

example : SignalSelection exampleSignals (.ofList [.bit]) :=
  (.nil : SignalSelection exampleSignals .nil).prepend .ready

def labels : SignalSelection signals types → List signals.Label
  | .nil => []
  | .cons label tail => label :: tail.labels

@[reducible] private def exampleControlSelection : SignalSelection exampleSignals
    (.ofList [.bit, .bit]) :=
  exampleSignals.selectionFrom [.valid, .ready]

@[reducible] private def exampleReversedSelection : SignalSelection exampleSignals
    (.ofList [.bit, .bit]) :=
  exampleSignals.selectionFrom [.ready, .valid]

example : exampleControlSelection.labels = [.valid, .ready] := rfl

/-- Selection order is independent of the signal map's canonical order. -/
example : exampleReversedSelection.labels = [.ready, .valid] := rfl

def project (selection : SignalSelection signals types)
    (values : signals.Values) : types.Denote :=
  match selection with
  | .nil => ()
  | .cons label tail => (values label, tail.project values)

@[reducible] private def exampleValues : exampleSignals.Values
  | .valid => true
  | .ready => false
  | .payload => fun _ => false

/-- Projection produces a tuple in selection order. -/
example : exampleControlSelection.project exampleValues = (true, (false, ())) := rfl

example : exampleReversedSelection.project exampleValues = (false, (true, ())) := rfl

end SignalSelection

def SignalMap.select (signals : SignalMap) (label : signals.Label) :
    SignalSelection signals (.cons (signals.signalType label) .nil) :=
  .cons label .nil

example : (exampleSignals.select .payload).labels = [.payload] := rfl

example : ((exampleSignals.select .payload).project
    SignalSelection.exampleValues).1 0 = false := by
  simp [SignalMap.select, SignalSelection.project, SignalSelection.exampleValues]

end Silean
