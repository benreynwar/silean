import Silean2.Foundation.SignalMap

namespace Silean2

/-! An ordered, typed selection of labels from a signal map. -/

inductive SignalSelection (signals : SignalMap) : SignalTypes → Type
  | nil : SignalSelection signals .nil
  | cons (label : signals.Label) (tail : SignalSelection signals types) :
      SignalSelection signals (.cons (signals.signalType label) types)

namespace SignalSelection

def prepend (tail : SignalSelection signals types) (label : signals.Label) :
    SignalSelection signals (.cons (signals.signalType label) types) :=
  .cons label tail

def labels : SignalSelection signals types → List signals.Label
  | .nil => []
  | .cons label tail => label :: tail.labels

def project (selection : SignalSelection signals types)
    (values : signals.Values) : types.Denote :=
  match selection with
  | .nil => ()
  | .cons label tail => (values label, tail.project values)

end SignalSelection

def SignalMap.select (signals : SignalMap) (label : signals.Label) :
    SignalSelection signals (.cons (signals.signalType label) .nil) :=
  .cons label .nil

end Silean2
