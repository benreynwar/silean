import HTFFT.Silean.InitialReorder.Lane.Lane
import Silean.Authoring.ModuleDesign
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.MuxDerived
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterDerived
import Silean.Modules.VectorConcat.VectorConcatDerived
import Silean.Modules.VectorReindex.VectorReindexDerived
import Silean.Modules.VectorSlice.VectorSliceDerived

namespace HTFFT.Silean.InitialReorder.Lane.Internal
open FFT

open _root_.Silean

def reverseLayout (configuration : Configuration depth) :
    Fin (configuration.laneDepth + InitialReorder.addressWidth configuration) →
      Fin (configuration.laneDepth + InitialReorder.addressWidth configuration) :=
  fun index => index.rev

end HTFFT.Silean.InitialReorder.Lane.Internal

namespace HTFFT.Silean
open FFT

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules

module_design InitialReorder.Lane (depth : Nat)
    (name := "InitialReorderLane")
    (configuration : Configuration depth)
    (lane : Fin (Configuration.laneCount configuration))
    (variant := s!"lane_{lane.val}")
    (specialization := [.natural depth, .natural configuration.laneDepth,
      .natural lane.val]) where
  boundary (InitialReorder.Lane.ports configuration)
    (naming := InitialReorder.Lane.Naming.ports configuration)
  instances {
    laneIndex := Constant.design (.vector configuration.laneDepth .bit)
      (BitVector.ofNat configuration.laneDepth lane.val),
    longAddress := VectorConcat.design .bit configuration.laneDepth
      (InitialReorder.addressWidth configuration),
    reversedLongAddress := VectorReindex.design .bit
      (configuration.laneDepth + InitialReorder.addressWidth configuration)
      (configuration.laneDepth + InitialReorder.addressWidth configuration)
      (InitialReorder.Lane.Internal.reverseLayout configuration),
    usedLongAddress := Mux.design (.vector
      (configuration.laneDepth + InitialReorder.addressWidth configuration) .bit),
    memoryAddress := VectorSlice.design .bit configuration.laneDepth
      (InitialReorder.addressWidth configuration) 0,
    payloadPack := NamedTupleCombiner.design
      (InitialReorder.Lane.payloadMap configuration) }
  wiring {
    outputs {
      .o_address := memoryAddress.result,
      .o_payload := payloadPack.value }
    instance (.laneIndex) {}
    instance (.longAddress) {
      .left := laneIndex.output,
      .right := input.i_cycleAddress }
    instance (.reversedLongAddress) {
      .input := longAddress.result }
    instance (.usedLongAddress) {
      .select := input.i_reversed,
      .whenFalse := longAddress.result,
      .whenTrue := reversedLongAddress.output }
    instance (.memoryAddress) {
      .value := usedLongAddress.result }
    instance (.payloadPack) {
      .data := input.i_data,
      .address := memoryAddress.result }
  }

end HTFFT.Silean
