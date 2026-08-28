import Silean.FIRRTL.Emit
import Silean.Emitters.StructuredPayload
import Silean.Modules.OneEntryFifo.OneEntryFifo

namespace Silean.Emitters.StructuredFifo

open Silean

def naming :=
  (Modules.OneEntryFifo.Naming.namingWith StructuredPayload.type
    StructuredPayload.naming).withKey
      ⟨"structured_fifo", "", []⟩

def firrtl : FIRRTL.RenderResult String :=
  FIRRTL.renderCircuit naming

end Silean.Emitters.StructuredFifo

def main (args : List String) : IO Unit :=
  Silean.FIRRTL.emitMain "emit-structured-fifo" args
    Silean.Emitters.StructuredFifo.firrtl
