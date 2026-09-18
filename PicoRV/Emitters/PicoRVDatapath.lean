import Silean.FIRRTL.Emit
import PicoRV.DatapathTheorems

def main (args : List String) : IO Unit :=
  Silean.FIRRTL.emitMain "emit-picorv-datapath" args
    (Silean.FIRRTL.renderClosedCircuit
      PicoRV.Datapath.naming)
