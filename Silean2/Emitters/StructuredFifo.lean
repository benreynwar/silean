import Silean2.FIRRTL.Emit
import Silean2.Modules.OneEntryFifo

namespace Silean2.Emitters.StructuredFifo

open Silean2

/-! Payload shape:
`{ a : Vector 3 Bit,
   b : { c : Bit, d : Vector 2 { e : Bit, f : Bit } } }`.

`SignalType` tuples are ordered structural products, so the source labels in
this comment correspond to tuple positions in the generated FIRRTL. -/

def elementType : SignalType :=
  .tuple (.cons .bit (.cons .bit .nil))

def bType : SignalType :=
  .tuple (.cons .bit (.cons (.vector 2 elementType) .nil))

def payloadType : SignalType :=
  .tuple (.cons (.vector 3 .bit) (.cons bType .nil))

def elementNaming : Naming.SignalTypeNaming elementType :=
  .tuple (.cons "e" .bit (.cons "f" .bit .nil))

def bNaming : Naming.SignalTypeNaming bType :=
  .tuple (.cons "c" .bit (.cons "d" (.vector elementNaming) .nil))

def payloadNaming : Naming.SignalTypeNaming payloadType :=
  .tuple (.cons "a" (.vector .bit) (.cons "b" bNaming .nil))

def naming :=
  (Modules.OneEntryFifo.Naming.namingWith payloadType payloadNaming).withKey
      ⟨"structured_fifo", "", []⟩

def firrtl : FIRRTL.RenderResult String :=
  FIRRTL.renderCircuit naming

end Silean2.Emitters.StructuredFifo

def main (args : List String) : IO Unit :=
  Silean2.FIRRTL.emitMain "emit-structured-fifo" args
    Silean2.Emitters.StructuredFifo.firrtl
