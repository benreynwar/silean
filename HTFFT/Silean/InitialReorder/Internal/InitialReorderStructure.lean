import HTFFT.Silean.InitialReorder.InitialReorder
import HTFFT.Silean.InitialReorder.Control.ControlDerived
import HTFFT.Silean.InitialReorder.BankLane.BankLaneDerived
import HTFFT.Silean.InitialReorder.Lane.LaneDerived
import Silean.Authoring.ModuleDesign
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.BarrelShifter.BarrelShifterDerived
import Silean.Modules.ConditionalNegate.ConditionalNegateDerived
import Silean.Modules.Constant.Constant
import Silean.Modules.OptionalShiftRegister.OptionalShiftRegisterDerived
import Silean.Modules.ShiftRegister.ShiftRegisterDerived
import Silean.Modules.VectorReindex.VectorReindexDerived
import Silean.Naming.SignalAdapterNaming
import Silean.Naming.PrimitiveNaming
import Silean.Primitives

/-! # Concrete VHDL-style initial reorder

The data is pre-rotated into one read-old register bank per lane.  Consecutive
frame traversals alternate between natural and bit-reversed bank addresses.
The registered bank outputs are rotated back into lane order, and a dedicated
delay keeps `o_first` aligned with the resulting frame.
-/

namespace HTFFT.Silean.InitialReorder.Internal
open FFT

open _root_.Silean
open _root_.Silean.Modules

abbrev sampleType (configuration : Configuration depth) : SignalType :=
  InitialReorder.Lane.sampleType configuration

abbrev barrelLatency (configuration : Configuration depth) : Nat :=
  configuration.initialBarrelPipeline.latency

abbrev laneCount (configuration : Configuration depth) : Nat :=
  2 ^ configuration.laneDepth

abbrev payloadType (configuration : Configuration depth) : SignalType :=
  InitialReorder.Lane.payloadType configuration

def laneRotationLayout (configuration : Configuration depth) :
    Fin configuration.laneDepth → Fin (addressWidth configuration) :=
  fun index => ⟨addressWidth configuration - 1 - index.val, by
    have indexLt := index.isLt
    have fits := laneDepth_le_addressWidth configuration
    omega⟩

@[reducible] def inputSplitter (configuration : Configuration depth) :
    Composition.SignalSplitter :=
  .vector configuration.laneCount (sampleType configuration)

@[reducible] def payloadCombiner (configuration : Configuration depth) :
    Composition.SignalCombiner :=
  .vector configuration.laneCount (payloadType configuration)

@[reducible] def payloadSplitter (configuration : Configuration depth) :
    Composition.SignalSplitter :=
  .vector configuration.laneCount (payloadType configuration)

@[reducible] def addressCombiner (configuration : Configuration depth) :
    Composition.SignalCombiner :=
  .vector configuration.laneCount
    (.vector (addressWidth configuration) .bit)

@[reducible] def addressSplitter (configuration : Configuration depth) :
    Composition.SignalSplitter :=
  .vector configuration.laneCount
    (.vector (addressWidth configuration) .bit)

@[reducible] def bankCombiner (configuration : Configuration depth) :
    Composition.SignalCombiner :=
  .vector configuration.laneCount (sampleType configuration)

theorem markerLatency_pos (configuration : Configuration depth) :
    0 < configuration.initialReorderLatency := by
  unfold Configuration.initialReorderLatency
  have := configuration.frameLength_pos
  omega

def markerDelayDesign (configuration : Configuration depth) :
    Naming.NamedModule :=
  ShiftRegister.design .bit configuration.initialReorderLatency
    (markerLatency_pos configuration)

def frameDelayDesign (configuration : Configuration depth)
    (signalType : SignalType) : Naming.NamedModule :=
  ShiftRegister.design signalType configuration.frameLength
    configuration.frameLength_pos

def specialization (configuration : Configuration depth) :
    List Naming.ModuleParameter :=
  [.natural depth,
   .natural configuration.laneDepth,
   .signalType (sampleType configuration)] ++
    (List.finRange (configuration.laneDepth + 1)).map fun boundary =>
      .boolean (configuration.initialBarrelPipeline.registerBoundary boundary)

end HTFFT.Silean.InitialReorder.Internal

namespace HTFFT.Silean
open FFT

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules

module_design InitialReorder (depth : Nat) (configuration : Configuration depth)
    (specialization := InitialReorder.Internal.specialization configuration) where
  boundary (InitialReorder.ports configuration)
    (naming := InitialReorder.Naming.ports configuration)
  instances {
    trueSource := Constant.design .bit true,
    control := InitialReorder.Control.design
      (InitialReorder.addressWidth configuration),
    laneRotation := VectorReindex.design .bit
      (InitialReorder.addressWidth configuration)
      configuration.laneDepth
      (InitialReorder.Internal.laneRotationLayout configuration),
    preRotation := ConditionalNegate.design configuration.laneDepth,
    preSplit := Naming.SignalAdapter.splitterDesign
      (InitialReorder.Internal.inputSplitter configuration),
    addressPayload
        (lane : Fin (InitialReorder.Internal.laneCount configuration) in
          Enumeration.fin (InitialReorder.Internal.laneCount configuration))
        (name := .indexed "address_payload" lane.val) :=
      InitialReorder.Lane.design depth configuration lane,
    payloadCombine := Naming.SignalAdapter.combinerDesign
      (InitialReorder.Internal.payloadCombiner configuration),
    preBarrel := BarrelShifter.design
      (InitialReorder.Internal.payloadType configuration)
      configuration.laneDepth configuration.initialBarrelPipeline,
    payloadSplit := Naming.SignalAdapter.splitterDesign
      (InitialReorder.Internal.payloadSplitter configuration),
    readCycleAlign := InitialReorder.Internal.frameDelayDesign configuration
      (.vector (InitialReorder.addressWidth configuration) .bit),
    readOrientationAlign :=
      InitialReorder.Internal.frameDelayDesign configuration .bit,
    readOrientationInvert := Primitives.notDesign,
    readRotationAlign := InitialReorder.Internal.frameDelayDesign configuration
      (.vector configuration.laneDepth .bit),
    readPreRotation := ConditionalNegate.design configuration.laneDepth,
    readAddressPayload
        (lane : Fin (InitialReorder.Internal.laneCount configuration) in
          Enumeration.fin (InitialReorder.Internal.laneCount configuration))
        (name := .indexed "read_address" lane.val) :=
      InitialReorder.Lane.design depth configuration lane,
    readAddressCombine := Naming.SignalAdapter.combinerDesign
      (InitialReorder.Internal.addressCombiner configuration),
    readPreBarrel := BarrelShifter.design
      (.vector (InitialReorder.addressWidth configuration) .bit)
      configuration.laneDepth configuration.initialBarrelPipeline,
    readAddressSplit := Naming.SignalAdapter.splitterDesign
      (InitialReorder.Internal.addressSplitter configuration),
    bank
        (lane : Fin (InitialReorder.Internal.laneCount configuration) in
          Enumeration.fin (InitialReorder.Internal.laneCount configuration))
        (name := .indexed "bank" lane.val) :=
      InitialReorder.BankLane.design depth configuration,
    bankCombine := Naming.SignalAdapter.combinerDesign
      (InitialReorder.Internal.bankCombiner configuration),
    postRotationAlign := OptionalShiftRegister.design
      (.vector configuration.laneDepth .bit)
      (InitialReorder.Internal.barrelLatency configuration + 1),
    postBarrel := BarrelShifter.design
      (InitialReorder.Internal.sampleType configuration)
      configuration.laneDepth configuration.initialBarrelPipeline,
    markerAlign := InitialReorder.Internal.markerDelayDesign configuration }
  wiring {
    outputs {
      .o_first := markerAlign.output,
      .o_data := postBarrel.result }
    instance (.trueSource) {}
    instance (.control) {
      .i_first := input.i_first }
    instance (.laneRotation) {
      .input := control.o_address }
    instance (.preRotation) {
      .value := laneRotation.output,
      .negate := trueSource.output }
    instance (.preSplit) {
      .value := input.i_data }
    instance (.addressPayload lane) {
      .i_data := preSplit[lane],
      .i_cycleAddress := control.o_address,
      .i_reversed := control.o_reversed }
    instance (.payloadCombine) {
      lane := addressPayload(lane)[.o_payload] }
    instance (.preBarrel) {
      .shift := preRotation.result,
      .data := payloadCombine.value }
    instance (.payloadSplit) {
      .value := preBarrel.result }
    instance (.readCycleAlign) {
      .input := control.o_address }
    instance (.readOrientationAlign) {
      .input := control.o_reversed }
    instance (.readOrientationInvert) {
      .input := readOrientationAlign.output }
    instance (.readRotationAlign) {
      .input := laneRotation.output }
    instance (.readPreRotation) {
      .value := readRotationAlign.output,
      .negate := trueSource.output }
    instance (.readAddressPayload lane) {
      .i_data := preSplit[lane],
      .i_cycleAddress := readCycleAlign.output,
      .i_reversed := readOrientationInvert.output }
    instance (.readAddressCombine) {
      lane := readAddressPayload(lane)[.o_address] }
    instance (.readPreBarrel) {
      .shift := readPreRotation.result,
      .data := readAddressCombine.value }
    instance (.readAddressSplit) {
      .value := readPreBarrel.result }
    instance (.bank lane) {
      .i_writePayload := payloadSplit[lane],
      .i_readAddress := readAddressSplit[lane] }
    instance (.bankCombine) {
      lane := bank(lane)[.o_data] }
    instance (.postRotationAlign) {
      .input := readRotationAlign.output }
    instance (.postBarrel) {
      .shift := postRotationAlign.output,
      .data := bankCombine.value }
    instance (.markerAlign) {
      .input := input.i_first }
  }

end HTFFT.Silean
