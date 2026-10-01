import HTFFT.Silean.InitialReorder.InitialReorder
import Silean.Authoring.ModulePorts
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter
import Silean.Modules.VectorConcat.VectorConcat
import Silean.Modules.VectorSlice.VectorSlice

/-! # One lane of initial-reorder address preparation

The VHDL architecture sends each sample through the pre-barrel shifter
together with the bank address derived from that sample's complete logical
index.  This combinational module gives that tagged payload a natural public
meaning.
-/

namespace HTFFT.Silean.InitialReorder.Lane
open FFT

open _root_.Silean
open _root_.Silean.Modules

abbrev sampleType (configuration : Configuration depth) : SignalType :=
  UnrolledFFTLayer.complexSignalType
    (configuration.arithmetic.boundaryFormat 0)

inductive PayloadField
  | data
  | address
deriving Enumeration

@[reducible] def payloadMap (configuration : Configuration depth) : SignalMap :=
  EnumeratedMap.of PayloadField fun
    | .data => sampleType configuration
    | .address => .vector (InitialReorder.addressWidth configuration) .bit

abbrev payloadType (configuration : Configuration depth) : SignalType :=
  (payloadMap configuration).tupleType

/-- The complete cycle-major logical address of one input lane. -/
def longAddress (configuration : Configuration depth)
    (lane : Fin configuration.laneCount)
    (cycleAddress : Fin (InitialReorder.addressWidth configuration) → Bool) :
    Fin (configuration.laneDepth +
      InitialReorder.addressWidth configuration) → Bool :=
  VectorConcat.concat (BitVector.ofNat configuration.laneDepth lane.val)
    cycleAddress

/-- Reverse every bit of a complete logical address. -/
def reverseLongAddress (configuration : Configuration depth)
    (address : Fin (configuration.laneDepth +
      InitialReorder.addressWidth configuration) → Bool) :
    Fin (configuration.laneDepth +
      InitialReorder.addressWidth configuration) → Bool :=
  fun index => address (Fin.rev index)

/-- Address stored alongside a lane's sample before bank selection. -/
def memoryAddress (configuration : Configuration depth)
    (lane : Fin configuration.laneCount)
    (cycleAddress : Fin (InitialReorder.addressWidth configuration) → Bool)
    (reversed : Bool) :
    Fin (InitialReorder.addressWidth configuration) → Bool :=
  VectorSlice.slice (prefixWidth := configuration.laneDepth)
    (suffixWidth := 0)
    (bif reversed then
      reverseLongAddress configuration (longAddress configuration lane cycleAddress)
    else longAddress configuration lane cycleAddress)

/-- Natural tagged payload carried through the pre-barrel shifter. -/
def resultValue (configuration : Configuration depth)
    (lane : Fin configuration.laneCount)
    (data : (sampleType configuration).Denote)
    (cycleAddress : Fin (InitialReorder.addressWidth configuration) → Bool)
    (reversed : Bool) : (payloadType configuration).Denote :=
  (payloadMap configuration).pack fun
    | .data => data
    | .address => memoryAddress configuration lane cycleAddress reversed

@[simp] theorem resultValue_address (configuration : Configuration depth)
    (lane : Fin configuration.laneCount)
    (data : (sampleType configuration).Denote)
    (cycleAddress : Fin (InitialReorder.addressWidth configuration) → Bool)
    (reversed : Bool) :
    NamedTupleSplitter.splitValue (payloadMap configuration)
        (resultValue configuration lane data cycleAddress reversed) .address =
      memoryAddress configuration lane cycleAddress reversed := by
  unfold resultValue
  rw [NamedTupleSplitter.splitValue_pack]

@[simp] theorem resultValue_data (configuration : Configuration depth)
    (lane : Fin configuration.laneCount)
    (data : (sampleType configuration).Denote)
    (cycleAddress : Fin (InitialReorder.addressWidth configuration) → Bool)
    (reversed : Bool) :
    NamedTupleSplitter.splitValue (payloadMap configuration)
        (resultValue configuration lane data cycleAddress reversed) .data =
      data := by
  unfold resultValue
  rw [NamedTupleSplitter.splitValue_pack]

module_ports ports (configuration : Configuration depth) where
  input i_data : sampleType configuration,
  input i_cycleAddress :
    .vector (InitialReorder.addressWidth configuration) .bit,
  input i_reversed : .bit,
  output o_address :
    .vector (InitialReorder.addressWidth configuration) .bit,
  output o_payload : payloadType configuration

end HTFFT.Silean.InitialReorder.Lane
