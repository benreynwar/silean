import Silean.FIRRTL.Emit
import Silean.Modules.Register.RegisterDerived

def main (args : List String) : IO Unit :=
  Silean.FIRRTL.emitMain "emit-bit-register" args
    (Silean.FIRRTL.renderCircuit
      (Silean.Modules.Register.Naming.naming .bit))
