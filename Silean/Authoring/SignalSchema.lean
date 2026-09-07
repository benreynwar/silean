import Silean.Naming.ModuleNaming

namespace Silean.Authoring

open Silean Silean.Naming

/-! # Aggregate signal naming schemas

A `SignalSchema` gives hierarchical emission names to the components of a
`SignalType`. The signal shape remains its type index, so a schema adds no
second structural representation and never enters hardware semantics or
proofs. It is an authoring name for `SignalTypeNaming`, with constructors that
make nested schema declarations read naturally.

Schemas are consumed by `signal_schema`, by the `(schema := ...)` modifier on
module ports, and ultimately by emitters that must preserve meaningful names
inside tuples and vectors.
-/

abbrev SignalSchema (signalType : SignalType) := SignalTypeNaming signalType

namespace SignalSchema

def bit : SignalSchema .bit := SignalTypeNaming.bit

def vector (length : Nat) (element : SignalSchema elementType) :
    SignalSchema (.vector length elementType) :=
  SignalTypeNaming.vector element

/-- Recover the shape carried by a schema's type index. -/
@[reducible] def signalType {signalType : SignalType}
    (_ : SignalSchema signalType) : SignalType := signalType

@[reducible] def positional (signalType : SignalType) : SignalSchema signalType :=
  SignalTypeNaming.positional signalType

end SignalSchema

end Silean.Authoring
