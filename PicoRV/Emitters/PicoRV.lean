import Silean.FIRRTL.Emit
import PicoRV.PicoRVSchedule

def main (args : List String) : IO Unit :=
  Silean.FIRRTL.emitMain "emit-picorv" args
    (Silean.FIRRTL.renderClosedCircuit
      PicoRV.PicoRV.naming)
