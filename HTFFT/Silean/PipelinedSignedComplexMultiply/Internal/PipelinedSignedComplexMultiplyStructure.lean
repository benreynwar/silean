import Silean.Authoring.ModuleDesign
import Silean.Modules.Add.AddDerived
import HTFFT.Silean.PipelinedSignedComplexMultiply.Internal.PipelinedSignedComplexMultiplyWidths
import Silean.Modules.OptionalShiftRegister.OptionalShiftRegisterDerived
import Silean.Modules.PipelinedSignedMultiply.PipelinedSignedMultiplyDerived
import Silean.Modules.SignedRoundShift.SignedRoundShiftDerived
import Silean.Modules.Sub.SubDerived
import Silean.Modules.VectorLayout.VectorLayoutDerived
import Silean.Naming.SignalAdapterNaming

/-! Structural implementation of the once-rounded complex multiplier. -/

namespace HTFFT.Silean.PipelinedSignedComplexMultiply.Internal

open _root_.Silean

def numeratorSplitter (leftWidth rightWidth : Nat) :
    Composition.SignalSplitter :=
  .vector 2 (.vector (numeratorWidth leftWidth rightWidth) .bit)

end HTFFT.Silean.PipelinedSignedComplexMultiply.Internal

namespace HTFFT.Silean

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules

module_design PipelinedSignedComplexMultiply
    (leftWidth : Nat) (rightWidth : Nat)
    (discardedWidth : Nat) (multiplierLatency : Nat)
    (registerBeforeRounding : Bool) where
  boundary
    (PipelinedSignedComplexMultiply.ports
      leftWidth rightWidth discardedWidth)
    (naming := PipelinedSignedComplexMultiply.Naming.ports
      leftWidth rightWidth discardedWidth)
  instances {
    realReal (name := .indexed "pipelined_signed_multiply" 0) :=
      PipelinedSignedMultiply.design leftWidth rightWidth multiplierLatency,
    imagImag (name := .indexed "pipelined_signed_multiply" 1) :=
      PipelinedSignedMultiply.design leftWidth rightWidth multiplierLatency,
    realImag (name := .indexed "pipelined_signed_multiply" 2) :=
      PipelinedSignedMultiply.design leftWidth rightWidth multiplierLatency,
    imagReal (name := .indexed "pipelined_signed_multiply" 3) :=
      PipelinedSignedMultiply.design leftWidth rightWidth multiplierLatency,
    realNumerator (name := .indexed "sub" 0) :=
      Sub.design
        (PipelinedSignedComplexMultiply.productWidth leftWidth rightWidth)
        (PipelinedSignedComplexMultiply.productWidth leftWidth rightWidth)
        true true true,
    imagNumerator (name := .indexed "add" 0) :=
      Add.design
        (PipelinedSignedComplexMultiply.productWidth leftWidth rightWidth)
        (PipelinedSignedComplexMultiply.productWidth leftWidth rightWidth)
        true true true,
    numeratorCombine (name := "combine_numerators") :=
      Naming.SignalAdapter.combinerDesign
        (PipelinedSignedComplexMultiply.Internal.numeratorSplitter
          leftWidth rightWidth).combiner,
    numeratorDelay (name := "register_before_rounding") :=
      OptionalShiftRegister.design
        (.vector 2 (.vector
          (PipelinedSignedComplexMultiply.numeratorWidth leftWidth rightWidth) .bit))
        (Bool.toNat registerBeforeRounding),
    numeratorSplit (name := "split_numerators") :=
      Naming.SignalAdapter.splitterDesign
        (PipelinedSignedComplexMultiply.Internal.numeratorSplitter
          leftWidth rightWidth),
    realRoundInput (name := .indexed "vector_layout" 0) :=
      VectorLayout.design
        (PipelinedSignedComplexMultiply.numeratorWidth leftWidth rightWidth)
        (PipelinedSignedComplexMultiply.Internal.roundInputWidth
          leftWidth rightWidth discardedWidth)
        (PipelinedSignedComplexMultiply.Internal.roundInputLayout
          leftWidth rightWidth discardedWidth),
    imagRoundInput (name := .indexed "vector_layout" 1) :=
      VectorLayout.design
        (PipelinedSignedComplexMultiply.numeratorWidth leftWidth rightWidth)
        (PipelinedSignedComplexMultiply.Internal.roundInputWidth
          leftWidth rightWidth discardedWidth)
        (PipelinedSignedComplexMultiply.Internal.roundInputLayout
          leftWidth rightWidth discardedWidth),
    realRound (name := .indexed "signed_round_shift" 0) :=
      SignedRoundShift.design
        (PipelinedSignedComplexMultiply.resultWidth
          leftWidth rightWidth discardedWidth)
        (PipelinedSignedComplexMultiply.Internal.effectiveDiscard
          leftWidth rightWidth discardedWidth),
    imagRound (name := .indexed "signed_round_shift" 1) :=
      SignedRoundShift.design
        (PipelinedSignedComplexMultiply.resultWidth
          leftWidth rightWidth discardedWidth)
        (PipelinedSignedComplexMultiply.Internal.effectiveDiscard
          leftWidth rightWidth discardedWidth) }
  wiring {
    outputs {
      .resultReal := realRound.result,
      .resultImag := imagRound.result }
    instance (.realReal) {
      .left := input.leftReal,
      .right := input.rightReal }
    instance (.imagImag) {
      .left := input.leftImag,
      .right := input.rightImag }
    instance (.realImag) {
      .left := input.leftReal,
      .right := input.rightImag }
    instance (.imagReal) {
      .left := input.leftImag,
      .right := input.rightReal }
    instance (.realNumerator) {
      .left := realReal.result,
      .right := imagImag.result }
    instance (.imagNumerator) {
      .left := realImag.result,
      .right := imagReal.result }
    instance (.numeratorCombine) {
      index := from (
        if first : index.val = 0 then
          (PipelinedSignedComplexMultiply.context leftWidth rightWidth
              discardedWidth multiplierLatency registerBeforeRounding)
            |>.instanceOutput .realNumerator .result
        else
          (PipelinedSignedComplexMultiply.context leftWidth rightWidth
              discardedWidth multiplierLatency registerBeforeRounding)
            |>.instanceOutput .imagNumerator .result) }
    instance (.numeratorDelay) {
      .input := numeratorCombine.value }
    instance (.numeratorSplit) {
      .value := numeratorDelay.output }
    instance (.realRoundInput) {
      .input := numeratorSplit[⟨0, by omega⟩] }
    instance (.imagRoundInput) {
      .input := numeratorSplit[⟨1, by omega⟩] }
    instance (.realRound) {
      .value := realRoundInput.output }
    instance (.imagRound) {
      .value := imagRoundInput.output }
  }

end HTFFT.Silean
