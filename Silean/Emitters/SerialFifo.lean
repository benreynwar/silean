import Silean.FIRRTL.Emit
import Silean.Modules.SerialDepthFifo.SerialDepthFifo

namespace Silean.Emitters.SerialFifo

open Silean

def depth : Nat := 2

def naming :=
  (Modules.SerialDepthFifo.design .bit depth
    (by unfold depth; omega)).naming.withKey
      ⟨"serial_fifo", "", []⟩

def firrtl : FIRRTL.RenderResult String :=
  FIRRTL.renderClosedCircuit naming

end Silean.Emitters.SerialFifo

def main (args : List String) : IO Unit :=
  Silean.FIRRTL.emitMain "emit-serial-fifo" args
    Silean.Emitters.SerialFifo.firrtl
