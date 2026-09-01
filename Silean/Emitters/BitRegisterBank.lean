import Silean.FIRRTL.Emit
import Silean.Modules.RegisterBank

namespace Silean.Emitters.BitRegisterBank

open Silean

def naming :=
  (Modules.RegisterBank.Naming.naming .bit 2 1).withKey
    ⟨"bit_register_bank", "", []⟩

def firrtl : FIRRTL.RenderResult String := FIRRTL.renderClosedCircuit naming

end Silean.Emitters.BitRegisterBank

def main (args : List String) : IO Unit :=
  Silean.FIRRTL.emitMain "emit-bit-register-bank" args
    Silean.Emitters.BitRegisterBank.firrtl
