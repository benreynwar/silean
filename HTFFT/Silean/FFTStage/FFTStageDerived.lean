import HTFFT.Silean.FFTStage.Internal.FFTStageVerification

/-! Public placement and correctness declarations for one rolled FFT stage. -/

namespace HTFFT.Silean.FFTStage

open _root_.Silean
open _root_.Silean.Authoring.CircuitDescription

/-- Place one concrete structural rolled FFT stage. -/
noncomputable def place
    (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (geometry : Geometry depth)
    (pipeline : PipelinedFixedButterfly.Pipeline)
    (twiddleDefinitionName : String)
    (i_first : Net .bit)
    (i_data : Net (.vector geometry.laneCount
      (complexSignalType
        (configuration.boundaryFormat geometry.stage.castSucc)))) :
    Builder (ports.OutputNets configuration geometry) :=
  ports.placeIndexed configuration geometry "fft_stage"
    (moduleStructure depth configuration table geometry pipeline
      twiddleDefinitionName)
    (naming depth configuration table geometry pipeline twiddleDefinitionName)
    i_first i_data

attribute [circuit_description] place

/-- The complete stage hierarchy has exactly one structural solution for
every boundary input and physical state. -/
theorem structuralCertification
    (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (geometry : Geometry depth)
    (pipeline : PipelinedFixedButterfly.Pipeline)
    (twiddleDefinitionName : String) :
    ModuleStructuralCertification
      (moduleStructure depth configuration table geometry pipeline
        twiddleDefinitionName) :=
  Internal.structuralCertification depth configuration table geometry pipeline
    twiddleDefinitionName

/-- Every concrete stage execution satisfies the natural framed fixed-point
stage contract at the exact structural latency. -/
theorem contract_of_execution
    (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (geometry : Geometry depth)
    (pipeline : PipelinedFixedButterfly.Pipeline)
    (twiddleDefinitionName : String)
    (twiddleFits : configuration.TwiddlesFit table)
    (carrier : configuration.ProductCarriersCover)
    {initialState finalState :
      (moduleStructure depth configuration table geometry pipeline
        twiddleDefinitionName).State}
    {inputs : List (ports configuration geometry).inputs.Values}
    {outputs : List (ports configuration geometry).outputs.Values}
    (execution :
      (moduleStructure depth configuration table geometry pipeline
        twiddleDefinitionName).Executes initialState inputs outputs finalState) :
    contract configuration table geometry (latency geometry pipeline)
      execution.toBoundaryTrace :=
  Internal.contract_of_execution depth configuration table geometry pipeline
    twiddleDefinitionName twiddleFits carrier execution

end HTFFT.Silean.FFTStage
