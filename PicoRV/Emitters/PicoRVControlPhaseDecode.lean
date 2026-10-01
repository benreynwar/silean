import Silean.FIRRTL.Emit
import PicoRV.Control.ControlPhaseDecodeDerived

def main (args : List String) : IO Unit :=
  Silean.FIRRTL.emitMain "emit-picorv-control-phase-decode" args
    (Silean.FIRRTL.renderCircuit
      PicoRV.Control.PhaseDecode.naming)
