import HTFFT.Silean.FFTStageLane.FFTStageLane
import HTFFT.Silean.PipelinedFixedButterfly.PipelinedFixedButterflyDerived
import Silean.Authoring.ModuleDesign
import Silean.Modules.Constant.Constant
import Silean.Modules.Mux.MuxDerived
import Silean.Modules.ROM.ROMDerived
import Silean.Modules.ShiftRegister.ShiftRegisterDerived
import Silean.Modules.VectorConcat.VectorConcatDerived

namespace HTFFT.Silean.FFTStageLane.Internal

open _root_.Silean
open HTFFT.FixedPoint

def laneAddress (laneAddressWidth lane : Nat) : Fin laneAddressWidth → Bool :=
  BitVector.ofNat laneAddressWidth lane

def pairDelayDesign (dataFormat : Format) (pairExponent : Nat) :
    Naming.NamedModule :=
  _root_.Silean.Modules.ShiftRegister.design
    (FFTStageLane.dataSignalType dataFormat) (2 ^ pairExponent)
      (Nat.two_pow_pos pairExponent)

def specialization (dataFormat twiddleFormat : Format) (pairDelay phaseWidth
    laneAddressWidth lane : Nat)
    (pipeline : PipelinedFixedButterfly.Pipeline) :
    List _root_.Silean.Naming.ModuleParameter :=
  [.natural dataFormat.width,
   .natural dataFormat.fractionalBits,
   .natural twiddleFormat.width,
   .natural twiddleFormat.fractionalBits,
   .natural pairDelay,
   .natural phaseWidth,
   .natural laneAddressWidth,
   .natural lane,
   .boolean pipeline.registerInputs,
   .natural pipeline.complexMultiply.multiplierLatency,
   .boolean pipeline.complexMultiply.registerBeforeRounding,
   .boolean pipeline.registerProduct,
   .boolean pipeline.registerOutputs]

end HTFFT.Silean.FFTStageLane.Internal

namespace HTFFT.Silean

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules
open HTFFT.FixedPoint

module_design FFTStageLane
    (dataFormat : Format) (twiddleFormat : Format)
    (pairExponent : Nat) (phaseWidth : Nat)
    (laneAddressWidth : Nat) (lane : Nat)
    (twiddleDefinitionName : String)
    (twiddleValues : Fin (ROM.entryCount (laneAddressWidth + phaseWidth)) →
      (FFTStageLane.twiddleSignalType twiddleFormat).Denote)
    (pipeline : PipelinedFixedButterfly.Pipeline)
    (variant := s!"lane_{lane}_{twiddleDefinitionName}")
    (specialization := FFTStageLane.Internal.specialization dataFormat
      twiddleFormat (2 ^ pairExponent) phaseWidth laneAddressWidth lane
      pipeline) where
  boundary (FFTStageLane.ports dataFormat twiddleFormat phaseWidth)
    (naming := FFTStageLane.Naming.ports dataFormat twiddleFormat phaseWidth)
  instances {
    laneAddress := Constant.design (.vector laneAddressWidth .bit)
      (FFTStageLane.Internal.laneAddress laneAddressWidth lane),
    addressConcat := VectorConcat.design .bit laneAddressWidth phaseWidth,
    twiddle := ROM.design twiddleDefinitionName
      (FFTStageLane.twiddleSignalType twiddleFormat)
      (laneAddressWidth + phaseWidth) twiddleValues,
    firstInputMux := Mux.design (FFTStageLane.dataSignalType dataFormat),
    secondInputMux := Mux.design (FFTStageLane.dataSignalType dataFormat),
    firstDelay := FFTStageLane.Internal.pairDelayDesign dataFormat pairExponent,
    secondDelay := FFTStageLane.Internal.pairDelayDesign dataFormat pairExponent,
    operandAMux := Mux.design (FFTStageLane.dataSignalType dataFormat),
    operandBMux := Mux.design (FFTStageLane.dataSignalType dataFormat),
    butterfly := PipelinedFixedButterfly.design
      dataFormat.width dataFormat.fractionalBits
      twiddleFormat.width twiddleFormat.fractionalBits
      pipeline.registerInputs
      pipeline.complexMultiply.multiplierLatency
      pipeline.complexMultiply.registerBeforeRounding
      pipeline.registerProduct pipeline.registerOutputs }
  wiring {
    outputs {
      .o_upper := butterfly.upper,
      .o_lower := butterfly.lower }
    instance (.laneAddress) {}
    instance (.addressConcat) {
      .left := laneAddress.output,
      .right := input.i_outputPhase }
    instance (.twiddle) {
      .address := addressConcat.result }
    instance (.firstInputMux) {
      .select := input.i_firstHalf,
      .whenFalse := input.i_branchB,
      .whenTrue := input.i_branchA }
    instance (.secondInputMux) {
      .select := input.i_firstHalf,
      .whenFalse := secondDelay.output,
      .whenTrue := input.i_branchB }
    instance (.firstDelay) {
      .input := firstInputMux.result }
    instance (.secondDelay) {
      .input := secondInputMux.result }
    instance (.operandAMux) {
      .select := input.i_firstHalf,
      .whenFalse := firstDelay.output,
      .whenTrue := secondDelay.output }
    instance (.operandBMux) {
      .select := input.i_firstHalf,
      .whenFalse := input.i_branchA,
      .whenTrue := firstDelay.output }
    instance (.butterfly) {
      .a := operandAMux.result,
      .b := operandBMux.result,
      .twiddle := twiddle.data }
  }

end HTFFT.Silean
