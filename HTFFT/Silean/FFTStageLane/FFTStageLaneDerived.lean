import HTFFT.Silean.FFTStageLane.Internal.FFTStageLaneVerification

/-! Public placement and correctness declarations for one rolled-stage lane. -/

namespace HTFFT.Silean.FFTStageLane

open _root_.Silean
open _root_.Silean.Authoring.CircuitDescription
open _root_.Silean.Modules
open HTFFT.FixedPoint

/-- Place one structural rolled-stage lane. -/
noncomputable def place
    (dataFormat twiddleFormat : Format)
    (pairExponent phaseWidth laneAddressWidth lane : Nat)
    (twiddleDefinitionName : String)
    (twiddleValues : Fin (ROM.entryCount (laneAddressWidth + phaseWidth)) →
      (twiddleSignalType twiddleFormat).Denote)
    (pipeline : PipelinedFixedButterfly.Pipeline)
    (i_firstHalf : Net .bit)
    (i_outputPhase : Net (.vector phaseWidth .bit))
    (i_branchA i_branchB : Net (dataSignalType dataFormat)) :
    Builder (ports.OutputNets dataFormat twiddleFormat phaseWidth) :=
  ports.placeIndexed dataFormat twiddleFormat phaseWidth
    "fft_stage_lane"
    (moduleStructure dataFormat twiddleFormat pairExponent phaseWidth
      laneAddressWidth lane twiddleDefinitionName twiddleValues pipeline)
    (naming dataFormat twiddleFormat pairExponent phaseWidth laneAddressWidth
      lane twiddleDefinitionName twiddleValues pipeline)
    i_firstHalf i_outputPhase i_branchA i_branchB

attribute [circuit_description] place

/-- The lane hierarchy has exactly one solution for every boundary input and
physical state. -/
theorem structuralCertification
    (dataFormat twiddleFormat : Format)
    (pairExponent phaseWidth laneAddressWidth lane : Nat)
    (twiddleDefinitionName : String)
    (twiddleValues : Fin (ROM.entryCount (laneAddressWidth + phaseWidth)) →
      (twiddleSignalType twiddleFormat).Denote)
    (pipeline : PipelinedFixedButterfly.Pipeline) :
    ModuleStructuralCertification
      (moduleStructure dataFormat twiddleFormat pairExponent phaseWidth
        laneAddressWidth lane twiddleDefinitionName twiddleValues pipeline) :=
  Internal.structuralCertification dataFormat twiddleFormat pairExponent
    phaseWidth laneAddressWidth lane twiddleDefinitionName twiddleValues pipeline

/-- Every structural lane execution satisfies its natural, state-hidden trace
contract. -/
theorem contract_of_execution
    (dataFormat twiddleFormat : Format)
    (pairExponent phaseWidth laneAddressWidth lane : Nat)
    (twiddleDefinitionName : String)
    (twiddleValues : Fin (ROM.entryCount (laneAddressWidth + phaseWidth)) →
      (twiddleSignalType twiddleFormat).Denote)
    (pipeline : PipelinedFixedButterfly.Pipeline)
    (carrier : PipelinedFixedButterfly.ProductCarrierCoversData
      dataFormat twiddleFormat)
    {initialState finalState :
      (moduleStructure dataFormat twiddleFormat pairExponent phaseWidth
        laneAddressWidth lane twiddleDefinitionName twiddleValues pipeline).State}
    {inputs : List (ports dataFormat twiddleFormat phaseWidth).inputs.Values}
    {outputs : List (ports dataFormat twiddleFormat phaseWidth).outputs.Values}
    (execution :
      (moduleStructure dataFormat twiddleFormat pairExponent phaseWidth
        laneAddressWidth lane twiddleDefinitionName twiddleValues pipeline)
        |>.Executes initialState inputs outputs finalState) :
    contract dataFormat twiddleFormat (2 ^ pairExponent)
      (Nat.two_pow_pos pairExponent) phaseWidth laneAddressWidth lane
      twiddleValues pipeline execution.toBoundaryTrace :=
  Internal.contract_of_execution dataFormat twiddleFormat pairExponent
    phaseWidth laneAddressWidth lane twiddleDefinitionName twiddleValues
    pipeline carrier execution

/-- Every structural lane execution supplies abstract traces for its two
commutator delay paths.  Endpoint states are existential and no physical
register representation escapes this theorem. -/
theorem delayTraces_of_execution
    (dataFormat twiddleFormat : Format)
    (pairExponent phaseWidth laneAddressWidth lane : Nat)
    (twiddleDefinitionName : String)
    (twiddleValues : Fin (ROM.entryCount (laneAddressWidth + phaseWidth)) →
      (twiddleSignalType twiddleFormat).Denote)
    (pipeline : PipelinedFixedButterfly.Pipeline)
    (carrier : PipelinedFixedButterfly.ProductCarrierCoversData
      dataFormat twiddleFormat)
    {initialState finalState :
      (moduleStructure dataFormat twiddleFormat pairExponent phaseWidth
        laneAddressWidth lane twiddleDefinitionName twiddleValues pipeline).State}
    {inputs : List (ports dataFormat twiddleFormat phaseWidth).inputs.Values}
    {outputs : List (ports dataFormat twiddleFormat phaseWidth).outputs.Values}
    (execution :
      (moduleStructure dataFormat twiddleFormat pairExponent phaseWidth
        laneAddressWidth lane twiddleDefinitionName twiddleValues pipeline)
        |>.Executes initialState inputs outputs finalState) :
    ∃ firstInitial firstFinal secondInitial secondFinal firstOutputs secondOutputs,
      Trace (_root_.Silean.DelayLine.Step (2 ^ pairExponent)) firstInitial
          (inputs.map (firstDelayInput dataFormat twiddleFormat phaseWidth))
          firstOutputs firstFinal ∧
        Trace (_root_.Silean.DelayLine.Step (2 ^ pairExponent)) secondInitial
          (secondDelayInputs dataFormat twiddleFormat phaseWidth inputs
            secondOutputs) secondOutputs secondFinal ∧
        firstOutputs.length = inputs.length ∧
        secondOutputs.length = inputs.length ∧
        FixedLatency.Relates pipeline.latency
          (outputRelation dataFormat twiddleFormat phaseWidth laneAddressWidth
            lane twiddleValues)
          (invocationsOf dataFormat twiddleFormat phaseWidth inputs
            firstOutputs secondOutputs) outputs :=
  Internal.delayTraces_of_execution dataFormat twiddleFormat pairExponent
    phaseWidth laneAddressWidth lane twiddleDefinitionName twiddleValues
    pipeline carrier execution

end HTFFT.Silean.FFTStageLane
