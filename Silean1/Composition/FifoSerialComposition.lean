import Silean.Contracts.Fifo.FifoCycleBehavior

namespace Silean.Composition.FifoSerial

open Silean
open Contracts.Fifo.Cycle
open Contracts.Cycle.Certification.Layer

/-! Connects two FIFO implementations in series. The upstream FIFO accepts the
external input, the downstream FIFO drives the external output, and their
valid/ready boundaries are connected internally. -/

inductive Instance
  /-- The FIFO nearest the external input. -/
  | upstream
  /-- The FIFO nearest the external output. -/
  | downstream
deriving Enumeration

@[reducible] def instancePorts (signalType : SignalType) : InstancePorts :=
  EnumeratedMap.of Instance fun _ => Silean.Interfaces.Fifo.ports signalType

@[reducible] def context (signalType : SignalType) : EndpointContext where
  ports := Silean.Interfaces.Fifo.ports signalType
  instancePorts := instancePorts signalType

def wiring (signalType : SignalType) :
    Wiring (context signalType).ports (context signalType).instancePorts :=
  let c := context signalType
  { moduleOutput := fun
    -- Outputs come from the corresponding end of the chain.
    | .outputValid => c.instanceOutput .downstream .outputValid
    | .outputData => c.instanceOutput .downstream .outputData
    | .inputReady => c.instanceOutput .upstream .inputReady
    instanceInput := fun
    -- External input enters the upstream FIFO; downstream readiness flows back.
    | .upstream, .inputValid => c.moduleInput .inputValid
    | .upstream, .inputData => c.moduleInput .inputData
    | .upstream, .outputReady => c.instanceOutput .downstream .inputReady
    | .upstream, .reset => c.moduleInput .reset
    -- Upstream output enters the downstream FIFO; external readiness terminates it.
    | .downstream, .inputValid => c.instanceOutput .upstream .outputValid
    | .downstream, .inputData => c.instanceOutput .upstream .outputData
    | .downstream, .outputReady => c.moduleInput .outputReady
    | .downstream, .reset => c.moduleInput .reset }

@[reducible] def body (signalType : SignalType) : ModuleBody :=
  ⟨context signalType, wiring signalType⟩

def moduleStructure (signalType : SignalType)
    (upstream downstream : ModuleStructure (Silean.Interfaces.Fifo.ports signalType)) :
    ModuleStructure (Silean.Interfaces.Fifo.ports signalType) :=
  .composite (body signalType) fun
    | .upstream => upstream
    | .downstream => downstream

end Silean.Composition.FifoSerial
