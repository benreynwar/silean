import HTFFT.Silean.FFTStageControl.FFTStageControl
import Silean.Authoring.ModuleDesign
import Silean.Composition.SignalAdapterImplementation
import Silean.Foundation.BitVector
import Silean.Modules.Constant.Constant
import Silean.Modules.EnabledResetCounter.EnabledResetCounterDerived
import Silean.Modules.Mux.MuxDerived
import Silean.Modules.ShiftRegister.ShiftRegisterDerived
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming
import Silean.Primitives.NotPrimitive

namespace HTFFT.Silean.FFTStageControl.Internal

open _root_.Silean

def phaseWidth (phaseExponent : Nat) := phaseExponent + 1

def phaseZero (phaseExponent : Nat) : Fin (phaseWidth phaseExponent) → Bool :=
  BitVector.ofNat (phaseWidth phaseExponent) 0

def phaseOne (phaseExponent : Nat) : Fin (phaseWidth phaseExponent) → Bool :=
  BitVector.ofNat (phaseWidth phaseExponent) 1

@[reducible] def phaseSplitter (phaseExponent : Nat) :
    Composition.SignalSplitter :=
  .vector (phaseWidth phaseExponent) .bit

def markerDelayDesign (phaseExponent : Nat) : Naming.NamedModule :=
  _root_.Silean.Modules.ShiftRegister.design .bit (2 ^ phaseExponent)
    (Nat.two_pow_pos phaseExponent)

end HTFFT.Silean.FFTStageControl.Internal

namespace HTFFT.Silean

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules

module_design FFTStageControl (phaseExponent : Nat) where
  boundary (FFTStageControl.ports
    (FFTStageControl.Internal.phaseWidth phaseExponent))
    (naming := FFTStageControl.Naming.ports
      (FFTStageControl.Internal.phaseWidth phaseExponent))
  instances {
    trueSource := Primitives.constantDesign true,
    phaseZero := Constant.design
      (.vector (FFTStageControl.Internal.phaseWidth phaseExponent) .bit)
      (FFTStageControl.Internal.phaseZero phaseExponent),
    inputPhaseCounter := EnabledResetCounter.design
      (FFTStageControl.Internal.phaseWidth phaseExponent)
      (FFTStageControl.Internal.phaseOne phaseExponent),
    inputPhaseSelect := Mux.design
      (.vector (FFTStageControl.Internal.phaseWidth phaseExponent) .bit),
    inputPhaseSplit := Naming.SignalAdapter.splitterDesign
      (FFTStageControl.Internal.phaseSplitter phaseExponent),
    firstHalf := Primitives.notDesign,
    markerDelay := FFTStageControl.Internal.markerDelayDesign phaseExponent,
    outputPhaseCounter := EnabledResetCounter.design
      (FFTStageControl.Internal.phaseWidth phaseExponent)
      (FFTStageControl.Internal.phaseOne phaseExponent),
    outputPhaseSelect := Mux.design
      (.vector (FFTStageControl.Internal.phaseWidth phaseExponent) .bit) }
  wiring {
    outputs {
      .o_delayedFirst := markerDelay.output,
      .o_firstHalf := firstHalf.output,
      .o_outputPhase := outputPhaseSelect.result }
    instance (.trueSource) {}
    instance (.phaseZero) {}
    instance (.inputPhaseCounter) {
      .enable := trueSource.output,
      .reset := input.i_first }
    instance (.inputPhaseSelect) {
      .select := input.i_first,
      .whenFalse := inputPhaseCounter.value,
      .whenTrue := phaseZero.output }
    instance (.inputPhaseSplit) {
      .value := inputPhaseSelect.result }
    instance (.firstHalf) {
      .input := inputPhaseSplit[Fin.last phaseExponent] }
    instance (.markerDelay) {
      .input := input.i_first }
    instance (.outputPhaseCounter) {
      .enable := trueSource.output,
      .reset := markerDelay.output }
    instance (.outputPhaseSelect) {
      .select := markerDelay.output,
      .whenFalse := outputPhaseCounter.value,
      .whenTrue := phaseZero.output }
  }

end HTFFT.Silean
