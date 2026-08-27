import Silean2.Naming

namespace Silean2.Emitters.StructuredPayload

open Silean2

/-! Shared backend fixture with enough hierarchy to exercise labelled tuple and
vector payload names through FIRRTL and flattened SystemVerilog ports.

`{ a : Vector 3 Bit,
   b : { c : Bit, d : Vector 2 { e : Bit, f : Bit } } }`. -/

def elementType : SignalType :=
  .tuple (.cons .bit (.cons .bit .nil))

def bType : SignalType :=
  .tuple (.cons .bit (.cons (.vector 2 elementType) .nil))

def type : SignalType :=
  .tuple (.cons (.vector 3 .bit) (.cons bType .nil))

def elementNaming : Naming.SignalTypeNaming elementType :=
  .tuple (.cons "e" .bit (.cons "f" .bit .nil))

def bNaming : Naming.SignalTypeNaming bType :=
  .tuple (.cons "c" .bit (.cons "d" (.vector elementNaming) .nil))

def naming : Naming.SignalTypeNaming type :=
  .tuple (.cons "a" (.vector .bit) (.cons "b" bNaming .nil))

end Silean2.Emitters.StructuredPayload
