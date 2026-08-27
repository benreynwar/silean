import Silean2.Examples.Fixtures.Not
import Silean2.Examples.Fixtures.DoubleNot

namespace Silean2.Examples.Checks.Endpoint

open Silean2

def moduleInput :
    SignalSource Examples.Fixtures.Not.ports Examples.Fixtures.Not.instances .bit :=
  Examples.Fixtures.Not.context.moduleInput .value

def inverterOutput :
    SignalSource Examples.Fixtures.Not.ports Examples.Fixtures.Not.instances .bit :=
  Examples.Fixtures.Not.context.instanceOutput .inverter .output

def moduleOutput :
    SignalSink Examples.Fixtures.Not.ports Examples.Fixtures.Not.instances .bit :=
  Examples.Fixtures.Not.context.moduleOutput .inverted

def inverterInput :
    SignalSink Examples.Fixtures.Not.ports Examples.Fixtures.Not.instances .bit :=
  Examples.Fixtures.Not.context.instanceInput .inverter .input

example : Examples.Fixtures.Not.wiring.drive inverterInput = moduleInput := rfl

example : Examples.Fixtures.Not.wiring.drive moduleOutput = inverterOutput := rfl

example : Examples.Fixtures.DoubleNot.instances.names.values =
    [Examples.Fixtures.DoubleNot.Instance.first, Examples.Fixtures.DoubleNot.Instance.second] := rfl

example : Examples.Fixtures.DoubleNot.wiring.moduleOutput .result =
    Examples.Fixtures.DoubleNot.context.instanceOutput .second .output := rfl

example : Examples.Fixtures.DoubleNot.wiring.instanceInput .first .input =
    Examples.Fixtures.DoubleNot.context.moduleInput .value := rfl

example : Examples.Fixtures.DoubleNot.wiring.instanceInput .second .input =
    Examples.Fixtures.DoubleNot.context.instanceOutput .first .output := rfl

end Silean2.Examples.Checks.Endpoint
