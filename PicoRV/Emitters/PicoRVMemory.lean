import Silean.FIRRTL.Emit
import PicoRV.Memory

def main (args : List String) : IO Unit :=
  Silean.FIRRTL.emitMain "emit-picorv-memory" args
    (Silean.FIRRTL.renderClosedCircuit
      PicoRV.Memory.naming)
