import Silean2.Emitters.StructuredPayload
import Silean2.FIRRTL.Emit
import Silean2.Modules.Fifo

namespace Silean2.Emitters.PointerFifo

open Silean2

def addressWidth : Nat := 2

def naming :=
  (Modules.Fifo.Naming.namingWith StructuredPayload.type addressWidth
    StructuredPayload.naming).withKey ⟨"pointer_fifo", "", []⟩

def firrtl : FIRRTL.RenderResult String :=
  FIRRTL.renderCircuit naming

end Silean2.Emitters.PointerFifo

def main (args : List String) : IO Unit :=
  Silean2.FIRRTL.emitMain "emit-pointer-fifo" args
    Silean2.Emitters.PointerFifo.firrtl
