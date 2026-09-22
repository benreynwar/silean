import HTFFT.Silean.PipelinedFixedButterfly.PipelinedFixedButterfly
import HTFFT.Silean.PipelinedSignedComplexMultiply.PipelinedSignedComplexMultiplyDerived
import Silean.Authoring.ModuleDesign
import Silean.Modules.Add.AddDerived
import Silean.Modules.OptionalShiftRegister.OptionalShiftRegisterDerived
import Silean.Modules.Sub.SubDerived
import Silean.Modules.VectorConcat.VectorConcatDerived
import Silean.Modules.VectorLayout.VectorLayoutDerived
import Silean.Modules.VectorSplit.VectorSplitDerived

/-! Structural implementation of the packed fixed-point butterfly. -/

namespace HTFFT.Silean

open _root_.Silean
open _root_.Silean.Authoring
open _root_.Silean.Modules

module_design PipelinedFixedButterfly
    (dataWidth : Nat) (dataFractionalBits : Nat)
    (twiddleWidth : Nat) (twiddleFractionalBits : Nat)
    (registerInputs : Bool) (multiplierLatency : Nat)
    (registerBeforeRounding : Bool) (registerProduct : Bool)
    (registerOutputs : Bool) where
  boundary
    (PipelinedFixedButterfly.ports
      ⟨dataWidth, dataFractionalBits⟩
      ⟨twiddleWidth, twiddleFractionalBits⟩)
    (naming := PipelinedFixedButterfly.Naming.ports
      ⟨dataWidth, dataFractionalBits⟩
      ⟨twiddleWidth, twiddleFractionalBits⟩)
  instances {
    aInputDelay (name := .indexed "input_register" 0) :=
      OptionalShiftRegister.design
        (.vector (dataWidth + dataWidth) .bit)
        (Bool.toNat registerInputs),
    bInputDelay (name := .indexed "input_register" 1) :=
      OptionalShiftRegister.design
        (.vector (dataWidth + dataWidth) .bit)
        (Bool.toNat registerInputs),
    twiddleInputDelay (name := .indexed "input_register" 2) :=
      OptionalShiftRegister.design
        (.vector (twiddleWidth + twiddleWidth) .bit)
        (Bool.toNat registerInputs),
    bSplit (name := .indexed "split_complex" 0) :=
      VectorSplit.design .bit dataWidth dataWidth,
    twiddleSplit (name := .indexed "split_complex" 1) :=
      VectorSplit.design .bit twiddleWidth twiddleWidth,
    product (name := "complex_multiply") :=
      PipelinedSignedComplexMultiply.design
        dataWidth twiddleWidth twiddleFractionalBits multiplierLatency
          registerBeforeRounding,
    productRealNarrow (name := .indexed "product_boundary" 0) :=
      VectorLayout.design
        (PipelinedSignedComplexMultiply.resultWidth
          dataWidth twiddleWidth twiddleFractionalBits)
        dataWidth
        (VectorLayout.extensionLayout true
          (PipelinedSignedComplexMultiply.resultWidth
            dataWidth twiddleWidth twiddleFractionalBits)
          dataWidth),
    productImagNarrow (name := .indexed "product_boundary" 1) :=
      VectorLayout.design
        (PipelinedSignedComplexMultiply.resultWidth
          dataWidth twiddleWidth twiddleFractionalBits)
        dataWidth
        (VectorLayout.extensionLayout true
          (PipelinedSignedComplexMultiply.resultWidth
            dataWidth twiddleWidth twiddleFractionalBits)
          dataWidth),
    productCombine (name := "combine_product") :=
      VectorConcat.design .bit dataWidth dataWidth,
    productDelay (name := "register_product") :=
      OptionalShiftRegister.design
        (.vector (dataWidth + dataWidth) .bit)
        (Bool.toNat registerProduct),
    productSplit (name := .indexed "split_complex" 2) :=
      VectorSplit.design .bit dataWidth dataWidth,
    aAlignDelay (name := "align_a") :=
      OptionalShiftRegister.design
        (.vector (dataWidth + dataWidth) .bit)
        (multiplierLatency + Bool.toNat registerBeforeRounding +
          Bool.toNat registerProduct),
    aSplit (name := .indexed "split_complex" 3) :=
      VectorSplit.design .bit dataWidth dataWidth,
    upperReal (name := .indexed "add" 0) :=
      Add.design dataWidth dataWidth true true true,
    upperImag (name := .indexed "add" 1) :=
      Add.design dataWidth dataWidth true true true,
    lowerReal (name := .indexed "sub" 0) :=
      Sub.design dataWidth dataWidth true true true,
    lowerImag (name := .indexed "sub" 1) :=
      Sub.design dataWidth dataWidth true true true,
    upperCombine (name := .indexed "combine_output" 0) :=
      VectorConcat.design .bit
        (PipelinedFixedButterfly.outputComponentWidth
          ⟨dataWidth, dataFractionalBits⟩)
        (PipelinedFixedButterfly.outputComponentWidth
          ⟨dataWidth, dataFractionalBits⟩),
    lowerCombine (name := .indexed "combine_output" 1) :=
      VectorConcat.design .bit
        (PipelinedFixedButterfly.outputComponentWidth
          ⟨dataWidth, dataFractionalBits⟩)
        (PipelinedFixedButterfly.outputComponentWidth
          ⟨dataWidth, dataFractionalBits⟩),
    upperOutputDelay (name := .indexed "output_register" 0) :=
      OptionalShiftRegister.design
        (.vector
          (PipelinedFixedButterfly.outputComponentWidth
              ⟨dataWidth, dataFractionalBits⟩ +
            PipelinedFixedButterfly.outputComponentWidth
              ⟨dataWidth, dataFractionalBits⟩) .bit)
        (Bool.toNat registerOutputs),
    lowerOutputDelay (name := .indexed "output_register" 1) :=
      OptionalShiftRegister.design
        (.vector
          (PipelinedFixedButterfly.outputComponentWidth
              ⟨dataWidth, dataFractionalBits⟩ +
            PipelinedFixedButterfly.outputComponentWidth
              ⟨dataWidth, dataFractionalBits⟩) .bit)
        (Bool.toNat registerOutputs) }
  wiring {
    outputs {
      .upper := upperOutputDelay.output,
      .lower := lowerOutputDelay.output }
    instance (.aInputDelay) {
      .input := input.a }
    instance (.bInputDelay) {
      .input := input.b }
    instance (.twiddleInputDelay) {
      .input := input.twiddle }
    instance (.bSplit) {
      .value := bInputDelay.output }
    instance (.twiddleSplit) {
      .value := twiddleInputDelay.output }
    instance (.product) {
      .leftReal := bSplit.right,
      .leftImag := bSplit.left,
      .rightReal := twiddleSplit.right,
      .rightImag := twiddleSplit.left }
    instance (.productRealNarrow) {
      .input := product.resultReal }
    instance (.productImagNarrow) {
      .input := product.resultImag }
    instance (.productCombine) {
      .left := productImagNarrow.output,
      .right := productRealNarrow.output }
    instance (.productDelay) {
      .input := productCombine.result }
    instance (.productSplit) {
      .value := productDelay.output }
    instance (.aAlignDelay) {
      .input := aInputDelay.output }
    instance (.aSplit) {
      .value := aAlignDelay.output }
    instance (.upperReal) {
      .left := aSplit.right,
      .right := productSplit.right }
    instance (.upperImag) {
      .left := aSplit.left,
      .right := productSplit.left }
    instance (.lowerReal) {
      .left := aSplit.right,
      .right := productSplit.right }
    instance (.lowerImag) {
      .left := aSplit.left,
      .right := productSplit.left }
    instance (.upperCombine) {
      .left := upperImag.result,
      .right := upperReal.result }
    instance (.lowerCombine) {
      .left := lowerImag.result,
      .right := lowerReal.result }
    instance (.upperOutputDelay) {
      .input := upperCombine.result }
    instance (.lowerOutputDelay) {
      .input := lowerCombine.result }
  }

end HTFFT.Silean
