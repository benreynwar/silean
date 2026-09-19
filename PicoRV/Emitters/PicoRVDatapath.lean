import Silean.FIRRTL.Emit
import PicoRV.Datapath

def main (args : List String) : IO Unit :=
  Silean.FIRRTL.emitMain "emit-picorv-datapath" args
    (Silean.FIRRTL.renderClosedCircuit
      PicoRV.Datapath.naming)
