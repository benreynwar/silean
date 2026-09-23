import HTFFT.Silean.UnrolledFFTLayer.Internal.UnrolledFFTLayerVerification

/-! Public placement and correctness declarations for one unrolled FFT layer. -/

namespace HTFFT.Silean.UnrolledFFTLayer

open _root_.Silean
open _root_.Silean.Authoring.CircuitDescription

/-- Place the structural butterfly bank for one layer. -/
noncomputable def place
    (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (stage : Fin depth)
    (input : Net (.vector (2 ^ depth)
      (complexSignalType
        (configuration.boundaryFormat stage.castSucc)))) :
    Builder (Net (.vector (2 ^ depth)
      (complexSignalType (configuration.boundaryFormat stage.succ)))) := do
  let outputs ← ports.placeIndexed configuration stage
    "unrolled_fft_layer"
    (moduleStructure depth configuration table stage)
    (naming depth configuration table stage)
    input
  pure outputs.output

attribute [circuit_description] place

/-- The generic layer hierarchy has exactly one solution for every input and
physical state. -/
theorem structuralCertification
    (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (stage : Fin depth) :
    ModuleStructuralCertification
      (moduleStructure depth configuration table stage) :=
  Internal.structuralCertification depth configuration table stage

/-- Every structural execution satisfies the natural vector-level fixed
latency contract. -/
theorem contract_of_execution
    (configuration : UnrolledFFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (stage : Fin depth)
    (twiddleFits : configuration.TwiddlesFit table)
    (carrier : configuration.ProductCarriersCover)
    {initialState finalState :
      (moduleStructure depth configuration table stage).State}
    {inputs : List (ports configuration stage).inputs.Values}
    {outputs : List (ports configuration stage).outputs.Values}
    (execution :
      (moduleStructure depth configuration table stage).Executes
        initialState inputs outputs finalState) :
    contract configuration table stage execution.toBoundaryTrace :=
  Internal.contract_of_execution depth configuration table stage
    twiddleFits carrier execution

end HTFFT.Silean.UnrolledFFTLayer
