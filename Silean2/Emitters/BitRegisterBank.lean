import Silean2.FIRRTL.Emit
import Silean2.Modules.RegisterBank

namespace Silean2.Emitters.BitRegisterBank

open Silean2

def naming :=
  (Modules.RegisterBank.Naming.naming .bit 2).withKey
    ⟨"bit_register_bank", "", []⟩

def firrtl : FIRRTL.RenderResult String := FIRRTL.renderCircuit naming

end Silean2.Emitters.BitRegisterBank

def main (args : List String) : IO Unit :=
  Silean2.FIRRTL.emitMain "emit-bit-register-bank" args
    Silean2.Emitters.BitRegisterBank.firrtl
