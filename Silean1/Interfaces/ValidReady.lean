import Silean.Foundation.ModulePorts
import Silean.Foundation.SignalSelection

namespace Silean.Interfaces

/-! Direction-correct valid/ready channels at a module boundary. Interfaces
select existing ports; they do not add ports or prescribe module latency. -/

/-- The valid, ready, and payload values observed for one channel cycle. -/
structure ValidReadySample (Payload : Type) where
  valid : Bool
  ready : Bool
  payload : Payload

namespace ValidReadySample

/-- Whether the sample transfers its payload. -/
def transfers (sample : ValidReadySample Payload) : Bool :=
  sample.valid && sample.ready

@[simp] theorem transfers_eq_true_iff (sample : ValidReadySample Payload) :
    sample.transfers = true ↔ sample.valid = true ∧ sample.ready = true := by
  simp [transfers]

/-- The payload when a transfer occurs. -/
def transferredPayload? (sample : ValidReadySample Payload) : Option Payload :=
  if sample.transfers then some sample.payload else none

@[simp] theorem transferredPayload?_eq_some_iff
    (sample : ValidReadySample Payload) (payload : Payload) :
    sample.transferredPayload? = some payload ↔
      sample.transfers = true ∧ sample.payload = payload := by
  simp [transferredPayload?]

@[simp] theorem transferredPayload?_eq_none_iff
    (sample : ValidReadySample Payload) :
    sample.transferredPayload? = none ↔ sample.transfers = false := by
  cases sample with
  | mk valid ready payload =>
      cases valid <;> cases ready <;> simp [transferredPayload?, transfers]

/-- The payloads transferred by a finite sequence of channel samples. -/
def transferredPayloads : List (ValidReadySample Payload) → List Payload
  | [] => []
  | sample :: samples =>
      match sample.transferredPayload? with
      | some payload => payload :: transferredPayloads samples
      | none => transferredPayloads samples

@[simp] theorem transferredPayloads_nil :
    transferredPayloads ([] : List (ValidReadySample Payload)) = [] := rfl

@[simp] theorem transferredPayloads_cons_transfer
    (sample : ValidReadySample Payload) (samples : List (ValidReadySample Payload))
    (transfers : sample.transfers = true) :
    transferredPayloads (sample :: samples) =
      sample.payload :: transferredPayloads samples := by
  simp [transferredPayloads, transferredPayload?, transfers]

@[simp] theorem transferredPayloads_cons_no_transfer
    (sample : ValidReadySample Payload) (samples : List (ValidReadySample Payload))
    (doesNotTransfer : sample.transfers = false) :
    transferredPayloads (sample :: samples) = transferredPayloads samples := by
  simp [transferredPayloads, transferredPayload?, doesNotTransfer]

@[simp] theorem transferredPayloads_append
    (left right : List (ValidReadySample Payload)) :
    transferredPayloads (left ++ right) =
      transferredPayloads left ++ transferredPayloads right := by
  induction left with
  | nil => rfl
  | cons sample samples induction =>
      simp only [List.cons_append, transferredPayloads]
      cases sample.transferredPayload? <;> simp [induction]

end ValidReadySample

/-- A valid/ready channel consumed by a module. Valid and payload are inputs;
ready is an output. -/
structure ValidReadySink (ports : ModulePorts) (payloadTypes : SignalTypes) where
  valid : ports.inputs.Label
  validType : ports.inputs.signalType valid = .bit
  ready : ports.outputs.Label
  readyType : ports.outputs.signalType ready = .bit
  payload : SignalSelection ports.inputs payloadTypes

/-- A valid/ready channel produced by a module. Valid and payload are outputs;
ready is an input. -/
structure ValidReadySource (ports : ModulePorts) (payloadTypes : SignalTypes) where
  valid : ports.outputs.Label
  validType : ports.outputs.signalType valid = .bit
  ready : ports.inputs.Label
  readyType : ports.inputs.signalType ready = .bit
  payload : SignalSelection ports.outputs payloadTypes

namespace ValidReadySink

/-- Observe one sink cycle from the module's input and output values. -/
def sample (interface : ValidReadySink ports payloadTypes)
    (inputs : ports.inputs.Values) (outputs : ports.outputs.Values) :
    ValidReadySample payloadTypes.Denote where
  valid := cast (congrArg SignalType.Denote interface.validType)
    (inputs interface.valid)
  ready := cast (congrArg SignalType.Denote interface.readyType)
    (outputs interface.ready)
  payload := interface.payload.project inputs

/-- Observe a finite sink trace whose cycle inputs and outputs are paired. -/
def samples (interface : ValidReadySink ports payloadTypes)
    (cycles : List (ports.inputs.Values × ports.outputs.Values)) :
    List (ValidReadySample payloadTypes.Denote) :=
  cycles.map fun cycle => interface.sample cycle.1 cycle.2

/-- Extract the payloads accepted by a finite sink trace. -/
def transferredPayloads (interface : ValidReadySink ports payloadTypes)
    (cycles : List (ports.inputs.Values × ports.outputs.Values)) :
    List payloadTypes.Denote :=
  ValidReadySample.transferredPayloads (interface.samples cycles)

@[simp] theorem samples_append (interface : ValidReadySink ports payloadTypes)
    (left right : List (ports.inputs.Values × ports.outputs.Values)) :
    interface.samples (left ++ right) = interface.samples left ++ interface.samples right := by
  simp [samples]

@[simp] theorem transferredPayloads_append
    (interface : ValidReadySink ports payloadTypes)
    (left right : List (ports.inputs.Values × ports.outputs.Values)) :
    interface.transferredPayloads (left ++ right) =
      interface.transferredPayloads left ++ interface.transferredPayloads right := by
  simp [transferredPayloads]

end ValidReadySink

namespace ValidReadySource

/-- Observe one source cycle from the module's input and output values. -/
def sample (interface : ValidReadySource ports payloadTypes)
    (inputs : ports.inputs.Values) (outputs : ports.outputs.Values) :
    ValidReadySample payloadTypes.Denote where
  valid := cast (congrArg SignalType.Denote interface.validType)
    (outputs interface.valid)
  ready := cast (congrArg SignalType.Denote interface.readyType)
    (inputs interface.ready)
  payload := interface.payload.project outputs

/-- Observe a finite source trace whose cycle inputs and outputs are paired. -/
def samples (interface : ValidReadySource ports payloadTypes)
    (cycles : List (ports.inputs.Values × ports.outputs.Values)) :
    List (ValidReadySample payloadTypes.Denote) :=
  cycles.map fun cycle => interface.sample cycle.1 cycle.2

/-- Extract the payloads emitted by a finite source trace. -/
def transferredPayloads (interface : ValidReadySource ports payloadTypes)
    (cycles : List (ports.inputs.Values × ports.outputs.Values)) :
    List payloadTypes.Denote :=
  ValidReadySample.transferredPayloads (interface.samples cycles)

@[simp] theorem samples_append (interface : ValidReadySource ports payloadTypes)
    (left right : List (ports.inputs.Values × ports.outputs.Values)) :
    interface.samples (left ++ right) = interface.samples left ++ interface.samples right := by
  simp [samples]

@[simp] theorem transferredPayloads_append
    (interface : ValidReadySource ports payloadTypes)
    (left right : List (ports.inputs.Values × ports.outputs.Values)) :
    interface.transferredPayloads (left ++ right) =
      interface.transferredPayloads left ++ interface.transferredPayloads right := by
  simp [transferredPayloads]

end ValidReadySource

end Silean.Interfaces
