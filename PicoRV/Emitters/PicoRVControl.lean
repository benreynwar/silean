import Silean.FIRRTL.Emit
import PicoRV.Control

def main (args : List String) : IO Unit :=
  Silean.FIRRTL.emitMain "emit-picorv-control" args
    (Silean.FIRRTL.renderClosedCircuit
      PicoRV.Control.naming)
