import Silean.FIRRTL.Emit
import PicoRV.Datapath

def main (args : List String) : IO Unit :=
  Silean.FIRRTL.emitMain "emit-picorv-datapath" args
    (Silean.FIRRTL.renderCircuit
      PicoRV.Datapath.naming)
