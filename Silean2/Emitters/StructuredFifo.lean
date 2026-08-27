import Silean2.FIRRTL.Emit
import Silean2.Emitters.StructuredPayload
import Silean2.Modules.OneEntryFifo

namespace Silean2.Emitters.StructuredFifo

open Silean2

def naming :=
  (Modules.OneEntryFifo.Naming.namingWith StructuredPayload.type
    StructuredPayload.naming).withKey
      ⟨"structured_fifo", "", []⟩

def firrtl : FIRRTL.RenderResult String :=
  FIRRTL.renderCircuit naming

end Silean2.Emitters.StructuredFifo

def main (args : List String) : IO Unit :=
  Silean2.FIRRTL.emitMain "emit-structured-fifo" args
    Silean2.Emitters.StructuredFifo.firrtl
