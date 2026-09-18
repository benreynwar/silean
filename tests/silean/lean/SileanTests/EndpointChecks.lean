import SileanTests.Fixtures.Not
import SileanTests.Fixtures.DoubleNot

namespace SileanTests.Endpoint

open Silean

def moduleInput :
    SignalSource SileanTests.Fixtures.Not.ports SileanTests.Fixtures.Not.instancePorts .bit :=
  SileanTests.Fixtures.Not.context.moduleInput .value

def inverterOutput :
    SignalSource SileanTests.Fixtures.Not.ports SileanTests.Fixtures.Not.instancePorts .bit :=
  SileanTests.Fixtures.Not.context.instanceOutput .inverter .output

def moduleOutput :
    SignalSink SileanTests.Fixtures.Not.ports SileanTests.Fixtures.Not.instancePorts .bit :=
  SileanTests.Fixtures.Not.context.moduleOutput .inverted

def inverterInput :
    SignalSink SileanTests.Fixtures.Not.ports SileanTests.Fixtures.Not.instancePorts .bit :=
  SileanTests.Fixtures.Not.context.instanceInput .inverter .input

example : SileanTests.Fixtures.Not.wiring.drive inverterInput = moduleInput := rfl

example : SileanTests.Fixtures.Not.wiring.drive moduleOutput = inverterOutput := rfl

example : SileanTests.Fixtures.DoubleNot.instancePorts.names.values =
    [SileanTests.Fixtures.DoubleNot.Instance.first, SileanTests.Fixtures.DoubleNot.Instance.second] := rfl

example : SileanTests.Fixtures.DoubleNot.wiring.moduleOutput .result =
    SileanTests.Fixtures.DoubleNot.context.instanceOutput .second .output := rfl

example : SileanTests.Fixtures.DoubleNot.wiring.instanceInput .first .input =
    SileanTests.Fixtures.DoubleNot.context.moduleInput .value := rfl

example : SileanTests.Fixtures.DoubleNot.wiring.instanceInput .second .input =
    SileanTests.Fixtures.DoubleNot.context.instanceOutput .first .output := rfl

end SileanTests.Endpoint
