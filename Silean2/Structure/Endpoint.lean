import Silean2.Structure.Instances

namespace Silean2

/-! Signal-producing and signal-consuming endpoints. The component vocabulary
is abstract; only its port function and the module's named instances are used.
The result type is indexed by the endpoint's structural signal type. -/

inductive SignalSource (ports : ModulePorts) (instances : Instances) :
    SignalType → Type
  | moduleInput (port : ports.inputs.Label) :
      SignalSource ports instances (ports.inputs.signalType port)
  | instanceOutput (name : instances.Name)
      (port : (instances.ports name).outputs.Label) :
      SignalSource ports instances
        ((instances.ports name).outputs.signalType port)

inductive SignalSink (ports : ModulePorts) (instances : Instances) :
    SignalType → Type
  | moduleOutput (port : ports.outputs.Label) :
      SignalSink ports instances (ports.outputs.signalType port)
  | instanceInput (name : instances.Name)
      (port : (instances.ports name).inputs.Label) :
      SignalSink ports instances
        ((instances.ports name).inputs.signalType port)

/-! The structural context shared by endpoint selection, wiring, and a module
body. It binds the arguments that otherwise repeat at every endpoint use. -/

structure EndpointContext where
  ports : ModulePorts
  instances : Instances

def EndpointContext.moduleInput (context : EndpointContext)
    (port : context.ports.inputs.Label) :
    SignalSource context.ports context.instances
      (context.ports.inputs.signalType port) :=
  .moduleInput port

def EndpointContext.moduleOutput (context : EndpointContext)
    (port : context.ports.outputs.Label) :
    SignalSink context.ports context.instances
      (context.ports.outputs.signalType port) :=
  .moduleOutput port

def EndpointContext.instanceOutput (context : EndpointContext)
    (name : context.instances.Name)
    (port : (context.instances.ports name).outputs.Label) :
    SignalSource context.ports context.instances
      ((context.instances.ports name).outputs.signalType port) :=
  .instanceOutput name port

def EndpointContext.instanceInput (context : EndpointContext)
    (name : context.instances.Name)
    (port : (context.instances.ports name).inputs.Label) :
    SignalSink context.ports context.instances
      ((context.instances.ports name).inputs.signalType port) :=
  .instanceInput name port

end Silean2
