import HTFFT.Silean.FinalReorder.Control.ControlDerived
import HTFFT.Silean.FinalReorder.Internal.FinalReorderSchedule
import Silean.Authoring.ModuleDesign
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.MuxDerived
import Silean.Modules.RegisterBank.RegisterBankDerived
import Silean.Modules.ShiftRegister.ShiftRegisterDerived
import Silean.Naming.SignalAdapterNaming

namespace HTFFT.Silean.FinalReorder.Internal
open FFT

open _root_.Silean
open _root_.Silean.Modules

abbrev addressWidth (configuration : Configuration depth) : Nat :=
  depth - configuration.laneDepth

theorem addressWidth_pos (configuration : Configuration depth) :
    0 < addressWidth configuration := by
  have geometry := configuration.initialReorderGeometry
  have lanePositive := configuration.laneDepth_pos
  unfold addressWidth
  omega

abbrev sampleType (configuration : Configuration depth) : SignalType :=
  UnrolledFFTLayer.complexSignalType
    (configuration.arithmetic.boundaryFormat (Fin.last depth))

abbrev halfVectorType (configuration : Configuration depth) : SignalType :=
  .vector (halfLaneCount configuration) (sampleType configuration)

@[reducible] def inputSplitter (configuration : Configuration depth) :
    Composition.SignalSplitter :=
  .vector configuration.laneCount (sampleType configuration)

@[reducible] def halfCombiner (configuration : Configuration depth) :
    Composition.SignalCombiner :=
  .vector (halfLaneCount configuration) (sampleType configuration)

@[reducible] def halfSplitter (configuration : Configuration depth) :
    Composition.SignalSplitter :=
  .vector (halfLaneCount configuration) (sampleType configuration)

@[reducible] def outputCombiner (configuration : Configuration depth) :
    Composition.SignalCombiner :=
  .vector configuration.laneCount (sampleType configuration)

def markerDelayDesign (configuration : Configuration depth) :
    Naming.NamedModule :=
  ShiftRegister.design .bit configuration.finalReorderLatency
    (Configuration.finalReorderLatency_pos configuration)

def specialization (configuration : Configuration depth) :
    List Naming.ModuleParameter :=
  [.natural depth,
   .natural configuration.laneDepth,
   .signalType (sampleType configuration)]

end HTFFT.Silean.FinalReorder.Internal

namespace HTFFT.Silean
open FFT

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules

module_design FinalReorder (depth : Nat)
    (configuration : FFT.Configuration depth)
    (specialization := FinalReorder.Internal.specialization configuration) where
  boundary (FinalReorder.ports configuration)
    (naming := FinalReorder.Naming.ports configuration)
  instances {
    trueSource := Constant.design .bit true,
    control := FinalReorder.Control.design
      (FinalReorder.Internal.addressWidth configuration),
    inputSplit := Naming.SignalAdapter.splitterDesign
      (FinalReorder.Internal.inputSplitter configuration),
    lowerCombine := Naming.SignalAdapter.combinerDesign
      (FinalReorder.Internal.halfCombiner configuration),
    upperCombine := Naming.SignalAdapter.combinerDesign
      (FinalReorder.Internal.halfCombiner configuration),
    bank0Write := Mux.design
      (FinalReorder.Internal.halfVectorType configuration),
    bank1Write := Mux.design
      (FinalReorder.Internal.halfVectorType configuration),
    bank0 := RegisterBank.design
      (FinalReorder.Internal.halfVectorType configuration)
      (FinalReorder.Internal.addressWidth configuration) 1,
    bank1 := RegisterBank.design
      (FinalReorder.Internal.halfVectorType configuration)
      (FinalReorder.Internal.addressWidth configuration) 1,
    bank1Bypass := Mux.design
      (FinalReorder.Internal.halfVectorType configuration),
    lowerOutput := Mux.design
      (FinalReorder.Internal.halfVectorType configuration),
    upperOutput := Mux.design
      (FinalReorder.Internal.halfVectorType configuration),
    lowerSplit := Naming.SignalAdapter.splitterDesign
      (FinalReorder.Internal.halfSplitter configuration),
    upperSplit := Naming.SignalAdapter.splitterDesign
      (FinalReorder.Internal.halfSplitter configuration),
    outputCombine := Naming.SignalAdapter.combinerDesign
      (FinalReorder.Internal.outputCombiner configuration),
    markerDelay := FinalReorder.Internal.markerDelayDesign configuration }
  wiring {
    outputs {
      .o_first := markerDelay.output,
      .o_data := outputCombine.value }
    instance (.trueSource) {}
    instance (.control) {
      .i_first := input.i_first,
      .i_readFirst := markerDelay.output }
    instance (.inputSplit) {
      .value := input.i_data }
    instance (.lowerCombine) {
      index := inputSplit[FinalReorder.Internal.lowerLane configuration index] }
    instance (.upperCombine) {
      index := inputSplit[FinalReorder.Internal.upperLane configuration index] }
    instance (.bank0Write) {
      .select := control.o_writeSwap,
      .whenFalse := lowerCombine.value,
      .whenTrue := upperCombine.value }
    instance (.bank1Write) {
      .select := control.o_writeSwap,
      .whenFalse := upperCombine.value,
      .whenTrue := lowerCombine.value }
    instance (.bank0) {
      .writeEnable := trueSource.output,
      .writeAddress := control.o_writeAddress0,
      .writeValue := bank0Write.result,
      (.readAddress 0) := control.o_readAddress }
    instance (.bank1) {
      .writeEnable := trueSource.output,
      .writeAddress := control.o_writeAddress1,
      .writeValue := bank1Write.result,
      (.readAddress 0) := control.o_readAddress }
    instance (.bank1Bypass) {
      .select := control.o_bypass,
      .whenFalse := bank1[.readValue 0],
      .whenTrue := bank1Write.result }
    instance (.lowerOutput) {
      .select := control.o_readSwap,
      .whenFalse := bank0[.readValue 0],
      .whenTrue := bank1Bypass.result }
    instance (.upperOutput) {
      .select := control.o_readSwap,
      .whenFalse := bank1Bypass.result,
      .whenTrue := bank0[.readValue 0] }
    instance (.lowerSplit) {
      .value := lowerOutput.result }
    instance (.upperSplit) {
      .value := upperOutput.result }
    instance (.outputCombine) {
      index := from (if lower : index.val <
          FinalReorder.Internal.halfLaneCount configuration then
        (context depth configuration).instanceOutput .lowerSplit
          ⟨index.val, lower⟩
      else
        (context depth configuration).instanceOutput .upperSplit
          ⟨index.val - FinalReorder.Internal.halfLaneCount configuration, by
            have bound := index.isLt
            have full := FinalReorder.Internal.two_mul_halfLaneCount configuration
            omega⟩) }
    instance (.markerDelay) {
      .input := input.i_first }
  }

end HTFFT.Silean
