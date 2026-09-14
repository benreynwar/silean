import Silean.FIRRTL.Emit
import Silean.Examples.PicoRV.DatapathCertified

def main (args : List String) : IO Unit :=
  Silean.FIRRTL.emitMain "emit-picorv-datapath" args
    (Silean.FIRRTL.renderClosedCircuit
      Silean.Examples.PicoRV.Datapath.naming)
