import Silean.FIRRTL.Emit
import Silean.Examples.PicoRV.MemoryTheorems

def main (args : List String) : IO Unit :=
  Silean.FIRRTL.emitMain "emit-picorv-memory" args
    (Silean.FIRRTL.renderClosedCircuit
      Silean.Examples.PicoRV.Memory.naming)
