import Silean2.FIRRTL.Emit
import Silean2.Modules.Register

def main (args : List String) : IO Unit :=
  Silean2.FIRRTL.emitMain "emit-bit-register" args
    (Silean2.FIRRTL.renderCircuit (Silean2.Modules.Register.Naming.naming .bit))
