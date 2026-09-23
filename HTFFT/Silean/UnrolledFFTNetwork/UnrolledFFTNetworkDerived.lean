import HTFFT.Silean.UnrolledFFTNetwork.Internal.UnrolledFFTNetworkVerification

/-! Public placement and correctness declarations for the generic unrolled
FFT network. -/

namespace HTFFT.Silean.UnrolledFFTNetwork

open _root_.Silean
open _root_.Silean.Authoring.CircuitDescription

/-- Place the complete ascending butterfly network.  The input is already in
bit-reversed order; `UnrolledFFT` supplies the natural-order wrapper. -/
noncomputable def place
    (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (input : Net (.vector (2 ^ depth)
      (UnrolledFFTLayer.complexSignalType
        (configuration.boundaryFormat 0)))) :
    Builder (Net (.vector (2 ^ depth)
      (UnrolledFFTLayer.complexSignalType
        (configuration.boundaryFormat (Fin.last depth))))) := do
  let outputs ← ports.placeIndexed configuration
    "unrolled_fft_network"
    (moduleStructure depth configuration table)
    (naming depth configuration table)
    input
  pure outputs.output

attribute [circuit_description] place

/-- The complete network hierarchy has exactly one structural solution for
every input and physical state. -/
theorem structuralCertification
    (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) :
    ModuleStructuralCertification
      (moduleStructure depth configuration table) :=
  Internal.structuralCertification depth configuration table

/-- Every structural execution satisfies the natural vector-level fixed
latency contract. -/
theorem contract_of_execution
    (configuration : UnrolledFFT.Configuration depth)
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

end HTFFT.Silean.UnrolledFFTNetwork
