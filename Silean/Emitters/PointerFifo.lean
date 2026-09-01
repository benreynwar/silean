import Silean.Emitters.StructuredPayload
import Silean.FIRRTL.Emit
import Silean.Modules.Fifo.Fifo

namespace Silean.Emitters.PointerFifo

open Silean

def addressWidth : Nat := 2

def naming :=
  (Modules.Fifo.Naming.namingWith StructuredPayload.type addressWidth
    StructuredPayload.naming).withKey ⟨"pointer_fifo", "", []⟩

def firrtl : FIRRTL.RenderResult String :=
  FIRRTL.renderClosedCircuit naming

end Silean.Emitters.PointerFifo

def main (args : List String) : IO Unit :=
  Silean.FIRRTL.emitMain "emit-pointer-fifo" args
    Silean.Emitters.PointerFifo.firrtl
