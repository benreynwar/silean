import Silean2.FIRRTL.Emit
import Silean2.FIRRTL.RegisterNaming

def main (args : List String) : IO Unit :=
  Silean2.FIRRTL.emitMain "emit-bit-register" args
    (Silean2.FIRRTL.RegisterNaming.firrtl .bit)
