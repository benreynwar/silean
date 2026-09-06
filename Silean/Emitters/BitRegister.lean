import Silean.FIRRTL.Emit
import Silean.Modules.Register.Register

def main (args : List String) : IO Unit :=
  Silean.FIRRTL.emitMain "emit-bit-register" args
    (Silean.FIRRTL.renderClosedCircuit
      (Silean.Modules.Register.Naming.naming .bit))
