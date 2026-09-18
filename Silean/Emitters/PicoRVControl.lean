import Silean.FIRRTL.Emit
import Silean.Examples.PicoRV.ControlTheorems

def main (args : List String) : IO Unit :=
  Silean.FIRRTL.emitMain "emit-picorv-control" args
    (Silean.FIRRTL.renderClosedCircuit
      Silean.Examples.PicoRV.Control.naming)
