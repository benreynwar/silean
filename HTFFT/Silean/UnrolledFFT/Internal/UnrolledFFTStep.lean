import HTFFT.Silean.UnrolledFFT.Internal.UnrolledFFTStructural

/-! One-cycle wiring equations for the natural-order FFT wrapper. -/

namespace HTFFT.Silean.UnrolledFFT.Internal

open _root_.Silean
open _root_.Silean.Modules

variable {depth : Nat} {configuration : Configuration depth}
  {table : HTFFT.Fixed.TwiddleTable depth}

/-- The static reindexer receives the parent input directly. -/
theorem reorderInput_of_solution
    {hierStep : HierStep (moduleStructure depth configuration table)}
    (satisfies :
      (moduleStructure depth configuration table).IsSolution hierStep) :
    (hierStep.children .reorder).inputs .input = hierStep.inputs .input := by
  have input := ModuleStructure.child_input satisfies (.reorder) (.input)
  simpa [wiring, EndpointContext.moduleInput, SignalSource.value] using input

/-- The ascending network receives the reindexer output. -/
theorem networkInput_of_solution
    {hierStep : HierStep (moduleStructure depth configuration table)}
    (satisfies :
      (moduleStructure depth configuration table).IsSolution hierStep) :
    (hierStep.children .network).inputs .input =
      (hierStep.children .reorder).outputs .output := by
  have input := ModuleStructure.child_input satisfies (.network) (.input)
  simpa [wiring, EndpointContext.instanceOutput, SignalSource.value] using input

/-- The parent output is the ascending network output. -/
theorem output_of_solution
    {hierStep : HierStep (moduleStructure depth configuration table)}
    (satisfies :
      (moduleStructure depth configuration table).IsSolution hierStep) :
    hierStep.outputs .output =
      (hierStep.children .network).outputs .output := by
  have output := ModuleStructure.parent_output satisfies (.output)
  simpa [wiring, EndpointContext.instanceOutput, SignalSource.value] using output

/-- The network input is exactly the ordinary Lean bit-reversal of the parent
sample vector. -/
theorem networkInput_eq_bitReverse_of_solution
    {hierStep : HierStep (moduleStructure depth configuration table)}
    (satisfies :
      (moduleStructure depth configuration table).IsSolution hierStep) :
    (hierStep.children .network).inputs .input =
      HTFFT.Exact.bitReverse (hierStep.inputs .input) := by
  have realizes := ModuleStructure.child_realizes satisfies (.reorder)
  simp only [structuralChildren] at realizes
  have reordered := VectorReindex.output_of_realization
    (UnrolledFFTLayer.complexSignalType
      (configuration.boundaryFormat 0))
    (2 ^ depth) (2 ^ depth) HTFFT.Exact.bitReverseIndex realizes
  simp only [HierStep.step_inputs, HierStep.step_outputs] at reordered
  rw [networkInput_of_solution satisfies, reordered,
    reorderInput_of_solution satisfies]
  rfl

end HTFFT.Silean.UnrolledFFT.Internal
