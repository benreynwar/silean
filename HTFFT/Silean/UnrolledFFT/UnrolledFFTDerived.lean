import HTFFT.Silean.UnrolledFFT.Internal.UnrolledFFTVerification
import HTFFT.Silean.UnrolledFFT.UnrolledFFTCorrectness

/-! Public placement and correctness declarations for the natural-order
unrolled FFT. -/

namespace HTFFT.Silean.UnrolledFFT

open _root_.Silean
open _root_.Silean.Authoring.CircuitDescription

/-- Place the complete natural-order unrolled FFT. -/
noncomputable def place
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (input : Net (.vector (2 ^ depth)
      (UnrolledFFTLayer.complexSignalType
        (configuration.boundaryFormat 0)))) :
    Builder (Net (.vector (2 ^ depth)
      (UnrolledFFTLayer.complexSignalType
        (configuration.boundaryFormat (Fin.last depth))))) := do
  let outputs ← ports.placeIndexed configuration
    "unrolled_fft"
    (moduleStructure depth configuration table)
    (naming depth configuration table)
    input
  pure outputs.output

attribute [circuit_description] place

/-- The natural-order wrapper has exactly one structural solution for every
input and physical state. -/
theorem structuralCertification
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) :
    ModuleStructuralCertification
      (moduleStructure depth configuration table) :=
  Internal.structuralCertification depth configuration table

/-- Every structural execution satisfies the pure fixed-point FFT contract. -/
theorem contract_of_execution
    (configuration : Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (twiddleFits : configuration.TwiddlesFit table)
    (carrier : configuration.ProductCarriersCover)
    {initialState finalState :
      (moduleStructure depth configuration table).State}
    {inputs : List (ports configuration).inputs.Values}
    {outputs : List (ports configuration).outputs.Values}
    (execution :
      (moduleStructure depth configuration table).Executes
        initialState inputs outputs finalState) :
    contract configuration table execution.toBoundaryTrace :=
  Internal.contract_of_execution depth configuration table
    twiddleFits carrier execution

end HTFFT.Silean.UnrolledFFT
