import Silean2.Examples.Not
import Silean2.Examples.DoubleNot

namespace Silean2.Examples.EndpointChecks

open Silean2

def moduleInput :
    SignalSource Examples.Not.ports Examples.Not.instances .bit :=
  Examples.Not.context.moduleInput .value

def inverterOutput :
    SignalSource Examples.Not.ports Examples.Not.instances .bit :=
  Examples.Not.context.instanceOutput .inverter .output

def moduleOutput :
    SignalSink Examples.Not.ports Examples.Not.instances .bit :=
  Examples.Not.context.moduleOutput .inverted

def inverterInput :
    SignalSink Examples.Not.ports Examples.Not.instances .bit :=
  Examples.Not.context.instanceInput .inverter .input

example : Examples.Not.wiring.drive inverterInput = moduleInput := rfl

example : Examples.Not.wiring.drive moduleOutput = inverterOutput := rfl

example : Examples.DoubleNot.instances.names.values =
    [Examples.DoubleNot.Instance.first, Examples.DoubleNot.Instance.second] := rfl

example : Examples.DoubleNot.wiring.moduleOutput .result =
    Examples.DoubleNot.context.instanceOutput .second .output := rfl

example : Examples.DoubleNot.wiring.instanceInput .first .input =
    Examples.DoubleNot.context.moduleInput .value := rfl

example : Examples.DoubleNot.wiring.instanceInput .second .input =
    Examples.DoubleNot.context.instanceOutput .first .output := rfl

end Silean2.Examples.EndpointChecks
