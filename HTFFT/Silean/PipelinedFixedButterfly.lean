import HTFFT.Fixed.ButterflyCorrectness
import HTFFT.Silean.PipelinedFixedButterfly.PipelinedFixedButterflyDerived

/-! Bridges from the structural butterfly trace to the pure fixed-point
butterfly model. -/

namespace HTFFT.Silean.PipelinedFixedButterfly

open HTFFT.FixedPoint

/-- At every valid delayed position, decoding the packed hardware outputs
gives exactly the pure fixed-point butterfly result.  This includes all
specified wrapping boundaries and therefore needs no dynamic range
hypothesis. -/
theorem output_eq_butterfly_of_execution
    (dataFormat twiddleFormat : Format) (pipeline : Pipeline)
    (carrier : ProductCarrierCoversData dataFormat twiddleFormat)
    {initialState finalState :
      (moduleStructure dataFormat.width dataFormat.fractionalBits
        twiddleFormat.width twiddleFormat.fractionalBits
        pipeline.registerInputs pipeline.complexMultiply.multiplierLatency
        pipeline.complexMultiply.registerBeforeRounding
        pipeline.registerProduct pipeline.registerOutputs).State}
    {inputs : List (ports dataFormat twiddleFormat).inputs.Values}
    {outputs : List (ports dataFormat twiddleFormat).outputs.Values}
    (execution :
      (moduleStructure dataFormat.width dataFormat.fractionalBits
        twiddleFormat.width twiddleFormat.fractionalBits
        pipeline.registerInputs pipeline.complexMultiply.multiplierLatency
        pipeline.complexMultiply.registerBeforeRounding
        pipeline.registerProduct pipeline.registerOutputs).Executes
          initialState inputs outputs finalState)
    (t : Nat) (inputInTrace : t < inputs.length)
    (outputInTrace : t + pipeline.latency < outputs.length) :
    let expected := resultValue dataFormat twiddleFormat
      (inputs.get ⟨t, inputInTrace⟩ .a)
      (inputs.get ⟨t, inputInTrace⟩ .b)
      (inputs.get ⟨t, inputInTrace⟩ .twiddle)
    decodeComplex (outputComponentWidth dataFormat)
        (outputs.get ⟨t + pipeline.latency, outputInTrace⟩ .upper) =
        expected.upper ∧
      decodeComplex (outputComponentWidth dataFormat)
        (outputs.get ⟨t + pipeline.latency, outputInTrace⟩ .lower) =
        expected.lower := by
  have delayed := _root_.Silean.FixedLatency.relation_at_of_trace execution
    (contract_of_execution dataFormat twiddleFormat pipeline carrier execution)
    t inputInTrace outputInTrace
  dsimp only
  rw [delayed.1, delayed.2]
  simp [resultValue, fixedConfig, HTFFT.Butterfly.Fixed.butterfly,
    HTFFT.Butterfly.Fixed.outputRounded,
    HTFFT.Butterfly.Fixed.Config.initial,
    HTFFT.Butterfly.Fixed.wrapComplex, HTFFT.Complex.map]

/-- When the explicit pure-model range conditions hold, the same decoded
hardware outputs equal the pre-wrap fixed-point result.  Thus the hardware
and pure integer calculation agree without modular overflow at any named
boundary. -/
theorem output_eq_outputRounded_of_execution
    (dataFormat twiddleFormat : Format) (pipeline : Pipeline)
    (carrier : ProductCarrierCoversData dataFormat twiddleFormat)
    {initialState finalState :
      (moduleStructure dataFormat.width dataFormat.fractionalBits
        twiddleFormat.width twiddleFormat.fractionalBits
        pipeline.registerInputs pipeline.complexMultiply.multiplierLatency
        pipeline.complexMultiply.registerBeforeRounding
        pipeline.registerProduct pipeline.registerOutputs).State}
    {inputs : List (ports dataFormat twiddleFormat).inputs.Values}
    {outputs : List (ports dataFormat twiddleFormat).outputs.Values}
    (execution :
      (moduleStructure dataFormat.width dataFormat.fractionalBits
        twiddleFormat.width twiddleFormat.fractionalBits
        pipeline.registerInputs pipeline.complexMultiply.multiplierLatency
        pipeline.complexMultiply.registerBeforeRounding
        pipeline.registerProduct pipeline.registerOutputs).Executes
          initialState inputs outputs finalState)
    (t : Nat) (inputInTrace : t < inputs.length)
    (outputInTrace : t + pipeline.latency < outputs.length)
    (noOverflow :
      let input := inputs.get ⟨t, inputInTrace⟩
      HTFFT.Butterfly.Fixed.NoOverflow
        (fixedConfig dataFormat twiddleFormat)
        (decodeComplex dataFormat.width (input .a))
        (decodeComplex dataFormat.width (input .b))
        (decodeComplex twiddleFormat.width (input .twiddle))) :
    let input := inputs.get ⟨t, inputInTrace⟩
    let expected := HTFFT.Butterfly.Fixed.outputRounded
      (fixedConfig dataFormat twiddleFormat)
      (decodeComplex dataFormat.width (input .a))
      (decodeComplex dataFormat.width (input .b))
      (decodeComplex twiddleFormat.width (input .twiddle))
    decodeComplex (outputComponentWidth dataFormat)
        (outputs.get ⟨t + pipeline.latency, outputInTrace⟩ .upper) =
        expected.upper ∧
      decodeComplex (outputComponentWidth dataFormat)
        (outputs.get ⟨t + pipeline.latency, outputInTrace⟩ .lower) =
        expected.lower := by
  have exactFixed := output_eq_butterfly_of_execution
    dataFormat twiddleFormat pipeline carrier execution
    t inputInTrace outputInTrace
  dsimp only at noOverflow ⊢
  rw [← HTFFT.Butterfly.Fixed.butterfly_eq_outputRounded_of_noOverflow
    noOverflow]
  exact exactFixed

end HTFFT.Silean.PipelinedFixedButterfly
