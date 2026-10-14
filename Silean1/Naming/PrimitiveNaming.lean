import Silean.Naming.ModuleNaming

namespace Silean.Naming.Primitive

open Silean Silean.Naming

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

def xor : ModuleNaming (ModuleStructure.primitive Primitives.xor) :=
  .primitive ⟨"xor", "bit", []⟩ binaryPorts emptySignals .xor

def eq : ModuleNaming (ModuleStructure.primitive Primitives.eq) :=
  .primitive ⟨"eq", "bit", []⟩ binaryPorts emptySignals .eq

def register : ModuleNaming (ModuleStructure.primitive Primitives.register) :=
  .primitive ⟨"register", "bit", []⟩ unaryPorts registerState .register

def constant (value : Bool) :
    ModuleNaming (ModuleStructure.primitive (Primitives.constant value)) :=
  .primitive ⟨"constant", if value then "true" else "false", []⟩
    { inputs := emptySignals
      outputs := ⟨fun | .output => "out"⟩ }
    emptySignals (.constant value)

end Silean.Naming.Primitive

namespace Silean.Primitives

/-- Primitive hardware definitions bundled with their default emission naming. -/
@[reducible] def notDesign : Naming.NamedModule :=
  ⟨not.ports, .primitive not, Naming.Primitive.not⟩

@[reducible] def andDesign : Naming.NamedModule :=
  ⟨and.ports, .primitive and, Naming.Primitive.and⟩

@[reducible] def orDesign : Naming.NamedModule :=
  ⟨or.ports, .primitive or, Naming.Primitive.or⟩

@[reducible] def xorDesign : Naming.NamedModule :=
  ⟨xor.ports, .primitive xor, Naming.Primitive.xor⟩

@[reducible] def eqDesign : Naming.NamedModule :=
  ⟨eq.ports, .primitive eq, Naming.Primitive.eq⟩

@[reducible] def registerDesign : Naming.NamedModule :=
  ⟨register.ports, .primitive register, Naming.Primitive.register⟩

@[reducible] def constantDesign (value : Bool) : Naming.NamedModule :=
  ⟨(constant value).ports, .primitive (constant value), Naming.Primitive.constant value⟩

end Silean.Primitives
