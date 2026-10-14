import Silean.Authoring.SignalSchemaDeclaration

namespace Silean.Emitters.StructuredPayload

open Silean
open Silean.Authoring

/-! Shared backend fixture with enough hierarchy to exercise labelled tuple and
vector payload names through FIRRTL and flattened SystemVerilog ports.

`{ a : Vector 3 Bit,
   b : { c : Bit, d : Vector 2 { e : Bit, f : Bit } } }`. -/

signal_schema Element where
  e : SignalSchema.bit,
  f : SignalSchema.bit

signal_schema B where
  c : SignalSchema.bit,
  d : SignalSchema.vector 2 Element.schema

signal_schema Payload where
  a : SignalSchema.vector 3 SignalSchema.bit,
  b : B.schema

abbrev elementType : SignalType := Element.signalType
abbrev bType : SignalType := B.signalType
abbrev type : SignalType := Payload.signalType

abbrev elementNaming : Naming.SignalTypeNaming elementType := Element.schema
abbrev bNaming : Naming.SignalTypeNaming bType := B.schema
abbrev naming : Naming.SignalTypeNaming type := Payload.schema

end Silean.Emitters.StructuredPayload
