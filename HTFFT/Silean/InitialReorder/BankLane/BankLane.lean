import HTFFT.Silean.InitialReorder.Lane.Lane
import Silean.Authoring.ModulePorts
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Modules.RegisterBank.RegisterBank
import Silean.Semantics.BoundaryTrace

/-! # One synchronous read-old lane of the initial reorder

This is the natural stateful boundary corresponding to one VHDL memory.  A
tagged sample is written every cycle.  The output is the registered value that
was read from the selected address on the preceding cycle.
-/

namespace HTFFT.Silean.InitialReorder.BankLane
open FFT

open _root_.Silean
open _root_.Silean.Modules

abbrev sampleType (configuration : Configuration depth) :=
  InitialReorder.Lane.sampleType configuration

abbrev payloadType (configuration : Configuration depth) :=
  InitialReorder.Lane.payloadType configuration

def payloadFields (configuration : Configuration depth)
    (payload : (payloadType configuration).Denote) :=
  NamedTupleSplitter.splitValue
    (InitialReorder.Lane.payloadMap configuration) payload

def payloadData (configuration : Configuration depth)
    (payload : (payloadType configuration).Denote) :
    (sampleType configuration).Denote :=
  payloadFields configuration payload .data

def payloadAddress (configuration : Configuration depth)
    (payload : (payloadType configuration).Denote) :
    Fin (InitialReorder.addressWidth configuration) → Bool :=
  payloadFields configuration payload .address

@[ext] structure State (configuration : Configuration depth) where
  entries : Fin (RegisterBank.entryCount
    (InitialReorder.addressWidth configuration)) →
      (sampleType configuration).Denote
  output : (sampleType configuration).Denote

module_ports ports (configuration : Configuration depth) where
  input i_writePayload : payloadType configuration,
  input i_readAddress :
    .vector (InitialReorder.addressWidth configuration) .bit,
  output o_data : sampleType configuration

def nextState (configuration : Configuration depth)
    (writePayload : (payloadType configuration).Denote)
    (readAddress : Fin (InitialReorder.addressWidth configuration) → Bool)
    (state : State configuration) : State configuration :=
  { entries := RegisterBank.nextEntries
      (InitialReorder.addressWidth configuration) true
      (payloadAddress configuration writePayload)
      (payloadData configuration writePayload) state.entries
    output := state.entries (BitVector.toIndex
      (InitialReorder.addressWidth configuration)
      readAddress) }

def Transition (configuration : Configuration depth)
    (input : (ports configuration).inputs.Values)
    (current : State configuration)
    (output : (ports configuration).outputs.Values)
    (next : State configuration) : Prop :=
  output .o_data = current.output ∧
    next = nextState configuration (input .i_writePayload)
      (input .i_readAddress) current

def contract (configuration : Configuration depth)
    (trace : BoundaryTrace (ports configuration)) : Prop :=
  ∃ initial final,
    Trace (Transition configuration) initial trace.inputs trace.outputs final

end HTFFT.Silean.InitialReorder.BankLane
