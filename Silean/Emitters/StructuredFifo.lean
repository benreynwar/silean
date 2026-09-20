import Silean.FIRRTL.Emit
import Silean.Emitters.StructuredPayload
import Silean.Modules.OneEntryFifo.OneEntryFifoDerived

namespace Silean.Emitters.StructuredFifo

open Silean

def naming :=
  (Modules.OneEntryFifo.namingWith StructuredPayload.type
    StructuredPayload.naming).withKey
      ⟨"structured_fifo", "", []⟩

def firrtl : FIRRTL.RenderResult String :=
  FIRRTL.renderClosedCircuit naming

end Silean.Emitters.StructuredFifo

def main (args : List String) : IO Unit :=
  Silean.FIRRTL.emitMain "emit-structured-fifo" args
    Silean.Emitters.StructuredFifo.firrtl
