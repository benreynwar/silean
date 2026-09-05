import Silean.Foundation.ModulePorts

namespace Silean

/-! # One uninstantiated structural layer

`ModuleBody` describes the parent boundary, named instance interfaces, and
complete typed wiring at one hierarchy level. It says how instances are
connected but not what implements them; `ModuleStructure.composite` separately
assigns a child structure to every instance name. Thus a body is a reusable
structural layer, while a module structure is a fully instantiated recursive
hierarchy. -/

/-- A canonically ordered collection of named child interfaces. -/
abbrev InstancePorts := EnumeratedMap ModulePorts

abbrev InstancePorts.Name (instancePorts : InstancePorts) := instancePorts.Key

abbrev InstancePorts.names (instancePorts : InstancePorts) := instancePorts.keys

abbrev InstancePorts.ports (instancePorts : InstancePorts) := instancePorts.value

/-- A signal produced by a module input or a child output. Its type records the
shape of the selected signal. -/
inductive SignalSource (ports : ModulePorts) (instancePorts : InstancePorts) :
    SignalType → Type
  | moduleInput (port : ports.inputs.Label) :
      SignalSource ports instancePorts (ports.inputs.signalType port)
  | instanceOutput (name : instancePorts.Name)
      (port : (instancePorts.ports name).outputs.Label) :
      SignalSource ports instancePorts
        ((instancePorts.ports name).outputs.signalType port)

namespace SignalSource

/-- Transport a source across a proved equality of signal shapes. This is
needed when a named structural selection is represented by its canonical tuple
position. -/
def castType {ports : ModulePorts} {instances : InstancePorts}
    {sourceType targetType : SignalType} (equal : sourceType = targetType)
    (source : SignalSource ports instances sourceType) :
    SignalSource ports instances targetType :=
  equal ▸ source

end SignalSource

/-- A signal consumed by a module output or a child input. Its type records the
shape of the selected signal. -/
inductive SignalSink (ports : ModulePorts) (instancePorts : InstancePorts) :
    SignalType → Type
  | moduleOutput (port : ports.outputs.Label) :
      SignalSink ports instancePorts (ports.outputs.signalType port)
  | instanceInput (name : instancePorts.Name)
      (port : (instancePorts.ports name).inputs.Label) :
      SignalSink ports instancePorts
        ((instancePorts.ports name).inputs.signalType port)

/-- The parent boundary and named child interfaces used by endpoints and
wiring. -/
structure EndpointContext where
  /-- Input and output ports of the parent module. -/
  ports : ModulePorts
  /-- Names and port shapes of every child instance. -/
  instancePorts : InstancePorts

def EndpointContext.moduleInput (context : EndpointContext)
    (port : context.ports.inputs.Label) :
    SignalSource context.ports context.instancePorts
      (context.ports.inputs.signalType port) :=
  .moduleInput port

def EndpointContext.moduleOutput (context : EndpointContext)
    (port : context.ports.outputs.Label) :
    SignalSink context.ports context.instancePorts
      (context.ports.outputs.signalType port) :=
  .moduleOutput port

def EndpointContext.instanceOutput (context : EndpointContext)
    (name : context.instancePorts.Name)
    (port : (context.instancePorts.ports name).outputs.Label) :
    SignalSource context.ports context.instancePorts
      ((context.instancePorts.ports name).outputs.signalType port) :=
  .instanceOutput name port

def EndpointContext.instanceInput (context : EndpointContext)
    (name : context.instancePorts.Name)
    (port : (context.instancePorts.ports name).inputs.Label) :
    SignalSink context.ports context.instancePorts
      ((context.instancePorts.ports name).inputs.signalType port) :=
  .instanceInput name port

/-- A driver for every parent output and child input. The types require each
driver to have the same signal shape as its sink. -/
structure Wiring (ports : ModulePorts) (instancePorts : InstancePorts) where
  moduleOutput : (port : ports.outputs.Label) →
    SignalSource ports instancePorts (ports.outputs.signalType port)
  instanceInput : (name : instancePorts.Name) →
    (port : (instancePorts.ports name).inputs.Label) →
    SignalSource ports instancePorts
      ((instancePorts.ports name).inputs.signalType port)

def Wiring.drive (wiring : Wiring ports instancePorts) :
    {signalType : SignalType} → SignalSink ports instancePorts signalType →
      SignalSource ports instancePorts signalType
  | _, .moduleOutput port => wiring.moduleOutput port
  | _, .instanceInput name port => wiring.instanceInput name port

/-! A structural module body owns its boundary, named instance interfaces, and
their complete wiring. The hierarchy layer supplies each child definition. -/

structure ModuleBody where
  /-- Parent ports and child instance interfaces. -/
  context : EndpointContext
  /-- Driver chosen for every parent output and child input. -/
  wiring : Wiring context.ports context.instancePorts

end Silean
