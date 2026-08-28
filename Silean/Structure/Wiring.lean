import Silean.Structure.Endpoint

namespace Silean

/-! Complete structural wiring. The two stored functions cover the two sink
forms separately for readable authoring; `drive` presents their single generic
meaning. -/

structure Wiring (ports : ModulePorts) (instances : Instances) where
  moduleOutput : (port : ports.outputs.Label) →
    SignalSource ports instances (ports.outputs.signalType port)
  instanceInput : (name : instances.Name) →
    (port : (instances.ports name).inputs.Label) →
    SignalSource ports instances
      ((instances.ports name).inputs.signalType port)

def Wiring.drive (wiring : Wiring ports instances) :
    {signalType : SignalType} → SignalSink ports instances signalType →
      SignalSource ports instances signalType
  | _, .moduleOutput port => wiring.moduleOutput port
  | _, .instanceInput name port => wiring.instanceInput name port

end Silean
