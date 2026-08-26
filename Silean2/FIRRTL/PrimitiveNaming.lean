import Silean2.FIRRTL.Naming

namespace Silean2.FIRRTL.PrimitiveNaming

open Silean2 Silean2.FIRRTL

def emptySignals : SignalMapNaming emptySignalMap :=
  ⟨fun signal => nomatch signal⟩

def registerState : SignalMapNaming Primitives.registerStateMap :=
  ⟨fun | .stored => "stored"⟩

def unaryPorts : ModulePortsNaming Primitives.unaryPorts where
  inputs := ⟨fun | .input => "in"⟩
  outputs := ⟨fun | .output => "out"⟩

def binaryPorts : ModulePortsNaming Primitives.binaryPorts where
  inputs := ⟨fun | .left => "left" | .right => "right"⟩
  outputs := ⟨fun | .output => "out"⟩

def not : ModuleNaming (ModuleStructure.primitive Primitives.not) :=
  .primitive ⟨"not", "bit", []⟩ unaryPorts emptySignals .not

def and : ModuleNaming (ModuleStructure.primitive Primitives.and) :=
  .primitive ⟨"and", "bit", []⟩ binaryPorts emptySignals .and

def or : ModuleNaming (ModuleStructure.primitive Primitives.or) :=
  .primitive ⟨"or", "bit", []⟩ binaryPorts emptySignals .or

def eq : ModuleNaming (ModuleStructure.primitive Primitives.eq) :=
  .primitive ⟨"eq", "bit", []⟩ binaryPorts emptySignals .eq

def register : ModuleNaming (ModuleStructure.primitive Primitives.register) :=
  .primitive ⟨"register", "bit", []⟩ unaryPorts registerState .register

end Silean2.FIRRTL.PrimitiveNaming
