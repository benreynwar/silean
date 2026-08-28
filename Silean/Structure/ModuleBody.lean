import Silean.Structure.Wiring

namespace Silean

/-! A structural module body owns its boundary, named instance interfaces, and
their complete wiring. The hierarchy layer supplies each child definition. -/

structure ModuleBody where
  context : EndpointContext
  wiring : Wiring context.ports context.instances

def ModuleBody.signature (body : ModuleBody) : ModuleSignature :=
  body.context.ports.signature

end Silean
