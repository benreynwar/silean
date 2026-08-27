import Silean2.Structure.Wiring

namespace Silean2

/-! A structural module body owns its boundary, named instance interfaces, and
their complete wiring. The hierarchy layer supplies each child definition. -/

structure ModuleBody where
  context : EndpointContext
  wiring : Wiring context.ports context.instances

def ModuleBody.signature (body : ModuleBody) : ModuleSignature :=
  body.context.ports.signature

end Silean2
