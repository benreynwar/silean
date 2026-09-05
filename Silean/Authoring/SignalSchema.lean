import Silean.Naming.ModuleNaming

namespace Silean.Authoring

open Silean Silean.Naming

/-! A schema is only the hierarchical naming metadata for a signal shape.
The shape itself is its type index, so schemas do not add another structural
representation and never enter hardware structures or proofs. Named tuple
declarations additionally generate typed field labels and a `SignalMap`. -/

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
