import HTFFT.Silean.FFTStage.Internal.FFTStageRefinement
import HTFFT.Silean.FFTStage.Internal.FFTStageScheduleCorrectness
import HTFFT.Silean.FFTStage.Internal.FFTStageStructural
import Silean.Semantics.StructuralObservation

/-! End-to-end certification of the concrete generic rolled FFT stage. -/

namespace HTFFT.Silean.FFTStage.Internal

open _root_.Silean
open _root_.Silean.Modules

private abbrev stageStructure
    (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (geometry : Geometry depth)
    (pipeline : PipelinedFixedButterfly.Pipeline)
    (twiddleDefinitionName : String) :=
  FFTStage.moduleStructure depth configuration table geometry pipeline
    twiddleDefinitionName

/-- Extract the state-hidden commutator witnesses and exact butterfly
relation supplied by one concrete child lane. -/
private theorem exists_laneEvidence_of_observed
    (depth : Nat) (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (geometry : Geometry depth)
    (pipeline : PipelinedFixedButterfly.Pipeline)
    (twiddleDefinitionName : String)
    {initialState finalState :
      (stageStructure configuration table geometry pipeline
        twiddleDefinitionName).State}
    {inputs : List (FFTStage.ports configuration geometry).inputs.Values}
    (hierarchy : List (HierStep (stageStructure configuration table geometry
      pipeline twiddleDefinitionName)))
    (observed : (stageStructure configuration table geometry pipeline
      twiddleDefinitionName).ObservedExecutes initialState inputs hierarchy
        finalState)
    (carrier : configuration.ProductCarriersCover)
    (lane : Fin (butterflyCount geometry)) :
    ∃ _evidence : LaneEvidence configuration table geometry pipeline
      twiddleDefinitionName hierarchy lane, True := by
  let laneExecution := observed.child (.lane lane)
  simp only [FFTStage.structuralChildren] at laneExecution
  obtain ⟨firstInitial, firstFinal, secondInitial, secondFinal,
      firstOutputs, secondOutputs, firstTrace, secondTrace,
      firstLength, secondLength, outputRelation⟩ :=
    FFTStageLane.delayTraces_of_execution
      (dataFormat configuration geometry)
      (configuration.twiddleFormat geometry.stage)
      (phaseExponent geometry) (phaseWidth geometry)
      (laneAddressWidth geometry) lane.val twiddleDefinitionName
      (twiddleValues configuration table geometry) pipeline
      (carrier geometry.stage) laneExecution
  refine ⟨{
      firstInitial := firstInitial
      firstFinal := firstFinal
      secondInitial := secondInitial
      secondFinal := secondFinal
      firstOutputs := firstOutputs
      secondOutputs := secondOutputs
      firstTrace := firstTrace
      secondTrace := secondTrace
      firstLength := firstLength
      secondLength := secondLength
      outputRelation := outputRelation }, trivial⟩

/-- The complete concrete marker path has exactly the advertised stage
latency. -/
theorem marker_computes_of_execution
    (depth : Nat) (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (geometry : Geometry depth)
    (pipeline : PipelinedFixedButterfly.Pipeline)
    (twiddleDefinitionName : String)
    {initialState finalState :
      (stageStructure configuration table geometry pipeline
        twiddleDefinitionName).State}
    {inputs : List (FFTStage.ports configuration geometry).inputs.Values}
    {outputs : List (FFTStage.ports configuration geometry).outputs.Values}
    (execution : (stageStructure configuration table geometry pipeline
      twiddleDefinitionName).Executes initialState inputs outputs finalState) :
    FixedLatency.Computes (FFTStage.latency geometry pipeline) id
      (inputs.map fun input => (input .i_first : Bool))
      (outputs.map fun output => (output .o_first : Bool)) := by
  obtain ⟨hierarchy, observed, rootOutputs⟩ := execution.observe
  let controlExecution := observed.child .control
  let markerExecution := observed.child .markerAlign
  simp only [FFTStage.structuralChildren] at controlExecution markerExecution
  have controlContract := FFTStageControl.contract_of_execution
    (phaseExponent geometry) controlExecution
  have controlMarker :=
    FFTStageControl.delayedFirst_computes_of_contract
      (phaseExponent geometry) controlContract
  have markerContract := OptionalShiftRegister.contract_of_execution .bit
    pipeline.latency markerExecution
  unfold OptionalShiftRegister.contract at markerContract
  have markerAlignedRaw :=
    FixedLatency.computes_of_holds_projection
      (function := id)
      (fun input : (ShiftRegister.ports .bit).inputs.Values =>
        (input .input : Bool))
      (fun output : (ShiftRegister.ports .bit).outputs.Values =>
        (output .output : Bool)) markerContract
  simp only [Trace.toBoundaryTrace_inputs, Trace.toBoundaryTrace_outputs]
    at markerAlignedRaw
  have markerAligned : FixedLatency.Computes pipeline.latency id
      (((hierarchy.map fun step =>
        (step.children .markerAlign).inputs).map fun input =>
          (input .input : Bool)))
      (((hierarchy.map fun step =>
        (step.children .markerAlign).outputs).map fun output =>
          (output .output : Bool))) := markerAlignedRaw
  have parentToControl :
      (inputs.map fun input => (input .i_first : Bool)) =
        ((hierarchy.map fun step => (step.children .control).inputs).map
          fun input => (input .i_first : Bool)) := by
    rw [← observed.hierarchy_inputs]
    simp only [List.map_map]
    apply List.map_congr_left
    intro step member
    exact (controlInput_of_solution
      (observed.solution_of_mem step member)).symm
  have controlToMarker :
      ((hierarchy.map fun step => (step.children .control).outputs).map
          fun output => (output .o_delayedFirst : Bool)) =
        ((hierarchy.map fun step => (step.children .markerAlign).inputs).map
          fun input => (input .input : Bool)) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro step member
    exact (markerWiring_of_solution
      (observed.solution_of_mem step member)).1.symm
  have markerToParent :
      ((hierarchy.map fun step => (step.children .markerAlign).outputs).map
          fun output => (output .output : Bool)) =
        (outputs.map fun output => (output .o_first : Bool)) := by
    rw [← rootOutputs]
    simp only [List.map_map]
    apply List.map_congr_left
    intro step member
    exact (markerWiring_of_solution
      (observed.solution_of_mem step member)).2.symm
  simp only [Trace.toBoundaryTrace_inputs, Trace.toBoundaryTrace_outputs]
    at controlMarker markerAligned
  have controlMarker := FixedLatency.computes_congr_inputs parentToControl.symm
    controlMarker
  have controlMarker := FixedLatency.computes_congr_outputs controlToMarker
    controlMarker
  have markerAligned := FixedLatency.computes_congr_outputs markerToParent
    markerAligned
  have serial := FixedLatency.computes_serial controlMarker markerAligned
  simpa [FFTStage.latency, FFTStageControl.pairDelay,
    pairDelay_eq_two_pow_phaseExponent, Function.comp_def, id_eq] using serial

/-- An arbitrary complete parent input window, followed by the required
pair-delay continuation, is observed by a refined lane as exactly the pure
commutator frame signal. -/
theorem laneVisible_eq_frameSignal
    (depth : Nat) (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (geometry : Geometry depth)
    (pipeline : PipelinedFixedButterfly.Pipeline)
    (twiddleDefinitionName : String)
    {initialState finalState :
      (stageStructure configuration table geometry pipeline
        twiddleDefinitionName).State}
    {inputs : List (FFTStage.ports configuration geometry).inputs.Values}
    (hierarchy : List (HierStep (stageStructure configuration table geometry
      pipeline twiddleDefinitionName)))
    (observed : (stageStructure configuration table geometry pipeline
      twiddleDefinitionName).ObservedExecutes initialState inputs hierarchy
        finalState)
    (controlInitial : FFTStageControl.State (phaseExponent geometry))
    (lane : Fin (butterflyCount geometry))
    (evidence : LaneEvidence configuration table geometry pipeline
      twiddleDefinitionName hierarchy lane)
    (start : Nat)
    (within : start + geometry.frameLength + geometry.pairDelay ≤ inputs.length)
    (cycle : Fin geometry.frameLength) :
    let inputFrame : FramedLatency.Frame geometry.frameLength
        (FFTStage.ports configuration geometry).inputs.Values :=
      FramedLatency.window inputs start (by omega)
    let toBank := fun
        (input : (FFTStage.ports configuration geometry).inputs.Values) =>
      bankInput geometry
        (FFTStage.inputObservation configuration geometry input).1
        (input .i_data)
    let preceding := (inputs.take start).map
      (fun input => CommutatorBank.laneInput (toBank input) lane)
    let first : Fin geometry.frameLength → Bool :=
      fun offset =>
        (FFTStage.inputObservation configuration geometry
          (inputFrame offset)).1
    let data : Fin geometry.frameLength → Fin geometry.laneCount →
        (dataSignalType configuration geometry).Denote :=
      fun offset =>
        inputFrame offset .i_data
    let continuationWindow := FramedLatency.window inputs
      (start + geometry.frameLength) (by omega)
    let continuation : Fin geometry.pairDelay →
        CommutatorBank.Input (butterflyCount geometry)
          ((dataSignalType configuration geometry).Denote) :=
      fun offset => bankInput geometry
        (FFTStage.inputObservation configuration geometry
          (continuationWindow offset)).1
        (continuationWindow offset .i_data)
    Commutator.visibleAt geometry.pairDelay
        (Geometry.pairDelay_pos geometry)
        (mergeState geometry controlInitial evidence.firstInitial
          evidence.secondInitial)
        (hierarchy.map fun step => laneBankInput geometry step.inputs lane)
        (start + geometry.pairDelay + cycle.val) (by
          simp only [List.length_map]
          rw [observed.length_eq]
          omega) =
      Commutator.frameSignal geometry.outputBoundary.groupCount
        geometry.pairDelay (Geometry.pairDelay_pos geometry)
        (Commutator.runDetailed geometry.pairDelay
          (Geometry.pairDelay_pos geometry)
          (mergeState geometry controlInitial evidence.firstInitial
            evidence.secondInitial) preceding).2
        (fun offset => CommutatorBank.laneInput
          (bankFrame geometry first data offset) lane)
        (fun offset => CommutatorBank.laneInput (continuation offset) lane)
        (Geometry.scheduleCycleEquiv geometry cycle) := by
  dsimp only
  let toBank := fun
      (input : (FFTStage.ports configuration geometry).inputs.Values) =>
    bankInput geometry
      (FFTStage.inputObservation configuration geometry input).1
      (input .i_data)
  let preceding := (inputs.take start).map
    (fun input => CommutatorBank.laneInput (toBank input) lane)
  let suffix := (inputs.drop
    (start + geometry.frameLength + geometry.pairDelay)).map
      (fun input => CommutatorBank.laneInput (toBank input) lane)
  let inputFrame : FramedLatency.Frame geometry.frameLength
      (FFTStage.ports configuration geometry).inputs.Values :=
    FramedLatency.window inputs start (by omega)
  let first : Fin geometry.frameLength → Bool :=
    fun offset =>
      (FFTStage.inputObservation configuration geometry
        (inputFrame offset)).1
  let data : Fin geometry.frameLength → Fin geometry.laneCount →
      (dataSignalType configuration geometry).Denote :=
    fun offset =>
      inputFrame offset .i_data
  let continuationWindow := FramedLatency.window inputs
    (start + geometry.frameLength) (by omega)
  let continuation : Fin geometry.pairDelay →
      CommutatorBank.Input (butterflyCount geometry)
        ((dataSignalType configuration geometry).Denote) :=
    fun offset => toBank (continuationWindow offset)
  have decomposed := FramedLatency.window_pair_decomposition inputs start
    geometry.frameLength geometry.pairDelay within
  have bankDecomposition :
      inputs.map toBank =
        (inputs.take start).map toBank ++
          List.ofFn (bankFrame geometry first data) ++
          List.ofFn continuation ++
          (inputs.drop
            (start + geometry.frameLength + geometry.pairDelay)).map toBank := by
    have mapped := congrArg (List.map toBank) decomposed
    simp only [List.map_append, List.map_ofFn, Function.comp_def] at mapped
    rw [ofFn_bankFrame geometry first data]
    convert mapped using 1
  have laneDecomposition :
      (hierarchy.map fun step => laneBankInput geometry step.inputs lane) =
        preceding ++
          Commutator.frameExecutionInputs
            geometry.outputBoundary.groupCount geometry.pairDelay
            (fun offset => CommutatorBank.laneInput
              (bankFrame geometry first data offset) lane)
            (fun offset => CommutatorBank.laneInput
              (continuation offset) lane) ++ suffix := by
    have mapped := congrArg
      (List.map fun input => CommutatorBank.laneInput input lane)
      bankDecomposition
    calc
      (hierarchy.map fun step => laneBankInput geometry step.inputs lane) =
          (hierarchy.map HierStep.inputs).map
            (fun input => CommutatorBank.laneInput (toBank input) lane) := by
        simp [List.map_map, laneBankInput, bankInput,
          CommutatorBank.laneInput, toBank, FFTStage.inputObservation]
      _ = inputs.map
            (fun input => CommutatorBank.laneInput (toBank input) lane) := by
        rw [observed.hierarchy_inputs]
      _ = _ := by
        simpa only [preceding, suffix, Commutator.frameExecutionInputs,
          List.map_map, List.map_append, List.map_ofFn,
          Function.comp_apply, Function.comp_def, List.append_assoc] using mapped
  have embedded := Commutator.visibleAt_embeddedFrame
    geometry.outputBoundary.groupCount geometry.pairDelay
    (Geometry.pairDelay_pos geometry)
    (mergeState geometry controlInitial evidence.firstInitial
      evidence.secondInitial)
    preceding suffix
    (fun offset => CommutatorBank.laneInput
      (bankFrame geometry first data offset) lane)
    (fun offset => CommutatorBank.laneInput (continuation offset) lane)
    (Geometry.scheduleCycleEquiv geometry cycle)
  let expanded := preceding ++
    Commutator.frameExecutionInputs
      geometry.outputBoundary.groupCount geometry.pairDelay
      (fun offset => CommutatorBank.laneInput
        (bankFrame geometry first data offset) lane)
      (fun offset => CommutatorBank.laneInput
        (continuation offset) lane) ++ suffix
  have originalOccurs :
      start + geometry.pairDelay + cycle.val <
        (hierarchy.map fun step => laneBankInput geometry step.inputs lane).length := by
    simp only [List.length_map]
    rw [observed.length_eq]
    omega
  have expandedOccurs :
      start + geometry.pairDelay + cycle.val < expanded.length := by
    unfold expanded
    rw [← laneDecomposition]
    exact originalOccurs
  have changed := Commutator.visibleAt_congr_inputs geometry.pairDelay
    (Geometry.pairDelay_pos geometry)
    (mergeState geometry controlInitial evidence.firstInitial
      evidence.secondInitial) laneDecomposition
    (start + geometry.pairDelay + cycle.val) originalOccurs expandedOccurs
  have startLe : start ≤ inputs.length := by omega
  have positionEqual :
      preceding.length + geometry.pairDelay +
          (Geometry.scheduleCycleEquiv geometry cycle).val =
        start + geometry.pairDelay + cycle.val := by
    simp [preceding, Nat.min_eq_left startLe]
  have embeddedOccurs :
      preceding.length + geometry.pairDelay +
          (Geometry.scheduleCycleEquiv geometry cycle).val < expanded.length := by
    rw [positionEqual]
    exact expandedOccurs
  have repositioned := Commutator.visibleAt_congr_position
    geometry.pairDelay (Geometry.pairDelay_pos geometry)
    (mergeState geometry controlInitial evidence.firstInitial
      evidence.secondInitial) expanded positionEqual embeddedOccurs expandedOccurs
  have result := changed.trans (repositioned.symm.trans embedded)
  convert result using 1

/-- Every concrete execution of the rolled stage satisfies its public,
state-hidden framed contract. -/
theorem contract_of_execution
    (depth : Nat) (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) (geometry : Geometry depth)
    (pipeline : PipelinedFixedButterfly.Pipeline)
    (twiddleDefinitionName : String)
    (twiddleFits : configuration.TwiddlesFit table)
    (carrier : configuration.ProductCarriersCover)
    {initialState finalState :
      (stageStructure configuration table geometry pipeline
        twiddleDefinitionName).State}
    {inputs : List (FFTStage.ports configuration geometry).inputs.Values}
    {outputs : List (FFTStage.ports configuration geometry).outputs.Values}
    (execution : (stageStructure configuration table geometry pipeline
      twiddleDefinitionName).Executes initialState inputs outputs finalState) :
    FFTStage.contract configuration table geometry
      (FFTStage.latency geometry pipeline) execution.toBoundaryTrace := by
  classical
  obtain ⟨hierarchy, observed, rootOutputs⟩ := execution.observe
  let controlExecution := observed.child .control
  simp only [FFTStage.structuralChildren] at controlExecution
  obtain ⟨controlInitial, controlFinal, controlTrace⟩ :=
    FFTStageControl.contract_of_execution
      (phaseExponent geometry) controlExecution
  have controlTrace' : Trace
      (FFTStageControl.Transition (phaseExponent geometry)) controlInitial
      (hierarchy.map fun step => (step.children .control).inputs)
      (hierarchy.map fun step => (step.children .control).outputs)
      controlFinal := by
    simpa only [Trace.toBoundaryTrace_inputs, Trace.toBoundaryTrace_outputs]
      using controlTrace
  have evidenceExists (lane : Fin (butterflyCount geometry)) :=
    exists_laneEvidence_of_observed depth configuration table geometry pipeline
      twiddleDefinitionName hierarchy observed carrier lane
  let evidence (lane : Fin (butterflyCount geometry)) :
      LaneEvidence configuration table geometry pipeline twiddleDefinitionName
        hierarchy lane :=
    Classical.choose (evidenceExists lane)
  have markerComputes := marker_computes_of_execution depth configuration table
    geometry pipeline twiddleDefinitionName execution
  have markerComputes' : FixedLatency.Computes
      (FFTStage.latency geometry pipeline) id
      (inputs.map fun input =>
        (FFTStage.inputObservation configuration geometry input).1)
      (outputs.map fun output =>
        (FFTStage.outputObservation configuration geometry output).1) := by
    simpa only [FFTStage.inputObservation, FFTStage.outputObservation] using
      markerComputes
  unfold FFTStage.contract FramedLatency.Holds
  rw [execution.toBoundaryTrace_inputs, execution.toBoundaryTrace_outputs]
  unfold FramedLatency.Relates
  constructor
  · exact execution.length_eq
  · intro start inputWithin outputWithin starts
    have outputStarts' :=
      FramedLatency.starts_of_fixedLatency_computes_projection
      (inputFirst := fun marker : Bool => marker = true)
      (outputFirst := fun marker : Bool => marker = true)
      markerComputes' start inputWithin outputWithin starts (by
        intro marker
        simp)
    refine ⟨?_, ?_⟩
    · exact outputStarts'
    unfold FFTStage.frameRelation FFTStage.carriedRelation
    let inputFrame : FramedLatency.Frame geometry.frameLength
        (FFTStage.ports configuration geometry).inputs.Values :=
      FramedLatency.window inputs start inputWithin
    let first : Fin geometry.frameLength → Bool :=
      fun cycle =>
        (FFTStage.inputObservation configuration geometry (inputFrame cycle)).1
    let data : InputFrame configuration geometry :=
      fun cycle => inputFrame cycle .i_data
    have continuationWithin :
        start + geometry.frameLength + geometry.pairDelay ≤ inputs.length := by
      rw [← execution.length_eq]
      unfold FFTStage.latency at outputWithin
      omega
    let continuationWindow := FramedLatency.window inputs
      (start + geometry.frameLength) continuationWithin
    let continuation : Fin geometry.pairDelay →
        CommutatorBank.Input (butterflyCount geometry)
          ((dataSignalType configuration geometry).Denote) :=
      fun offset => bankInput geometry
        (FFTStage.inputObservation configuration geometry
          (continuationWindow offset)).1
        (continuationWindow offset .i_data)
    let preceding (lane : Fin (butterflyCount geometry)) :=
      (inputs.take start).map (fun input =>
        CommutatorBank.laneInput
          (bankInput geometry
            (FFTStage.inputObservation configuration geometry input).1
            (input .i_data)) lane)
    let bankState : CommutatorBank.State (butterflyCount geometry)
        geometry.pairDelay
        ((dataSignalType configuration geometry).Denote) :=
      fun lane =>
        (Commutator.runDetailed geometry.pairDelay
          (Geometry.pairDelay_pos geometry)
          (mergeState geometry controlInitial (evidence lane).firstInitial
            (evidence lane).secondInitial)
          (preceding lane)).2
    have firstStarts : FramedLatency.Starts geometry.frameLength_pos
        (fun marker : Bool => marker = true) first := by
      constructor
      · simpa only [first, inputFrame] using starts.1
      · intro offset nonzero
        simpa only [first, inputFrame] using starts.2 offset nonzero
    have scheduled := outputFrameOfBankFrameSignals_eq_contractResult
      configuration table geometry bankState first data continuation firstStarts
    change (fun cycle : Fin geometry.frameLength =>
      fun sample : Fin geometry.outputBoundary.laneCount =>
        (FramedLatency.window outputs
          (start + FFTStage.latency geometry pipeline) outputWithin cycle)
            .o_data (Fin.cast (by rfl) sample)) =
      FFTStage.encodeOutputFrame configuration geometry
        (FFTStage.resultValue configuration table geometry data)
    rw [← scheduled]
    funext cycle physicalLane
    let laneCoordinate := geometry.outputBoundary.laneEquiv physicalLane
    let lane : Fin (butterflyCount geometry) := laneCoordinate.2
    let sourceTime := start + geometry.pairDelay + cycle.val
    have sourceInHierarchy : sourceTime < hierarchy.length := by
      rw [observed.length_eq]
      unfold sourceTime
      omega
    have finalInHierarchy :
        sourceTime + pipeline.latency < hierarchy.length := by
      rw [observed.length_eq, ← execution.length_eq]
      simp only [sourceTime]
      simp only [FFTStage.latency] at outputWithin
      omega
    have outputIndexInTrace :
        start + FFTStage.latency geometry pipeline + cycle.val < outputs.length := by
      omega
    let finalStep := hierarchy.get
      ⟨sourceTime + pipeline.latency, finalInHierarchy⟩
    have finalSolution := observed.solution_at
      (sourceTime + pipeline.latency) finalInHierarchy
    have finalAt := observed.output_at rootOutputs
      (sourceTime + pipeline.latency) finalInHierarchy (by
        unfold sourceTime
        unfold FFTStage.latency at outputIndexInTrace
        omega)
    have laneRelated := laneOutputRelation_at configuration table geometry
      pipeline twiddleDefinitionName lane hierarchy
      (fun step member => observed.solution_of_mem step member)
      controlInitial controlFinal controlTrace' (evidence lane) sourceTime
      sourceInHierarchy finalInHierarchy
    unfold FFTStageLane.outputRelation at laneRelated
    dsimp only at laneRelated
    rw [laneResultValue_eq configuration table geometry twiddleFits]
      at laneRelated
    have visibleEqual := laneVisible_eq_frameSignal depth configuration table
      geometry pipeline twiddleDefinitionName hierarchy observed controlInitial
      lane (evidence lane) start continuationWithin cycle
    have visibleEqual' :
        Commutator.visibleAt geometry.pairDelay
            (Geometry.pairDelay_pos geometry)
            (mergeState geometry controlInitial (evidence lane).firstInitial
              (evidence lane).secondInitial)
            (hierarchy.map fun step => laneBankInput geometry step.inputs lane)
            sourceTime (by simpa using sourceInHierarchy) =
          bankFrameSignals configuration geometry bankState first data
            continuation cycle lane := by
      convert visibleEqual using 1
      unfold bankFrameSignals bankState preceding continuation first data
        inputFrame continuationWindow CommutatorBank.frameSignal
      rfl
    have parentOutput := outputBoundarySample_of_solution finalSolution
      physicalLane
    have outputIndexEqual :
        (⟨start + FFTStage.latency geometry pipeline + cycle.val,
          outputIndexInTrace⟩ : Fin outputs.length) =
        ⟨sourceTime + pipeline.latency, by
          unfold sourceTime
          unfold FFTStage.latency at outputIndexInTrace
          omega⟩ := by
      apply Fin.ext
      change start + FFTStage.latency geometry pipeline + cycle.val =
        sourceTime + pipeline.latency
      unfold sourceTime FFTStage.latency
      omega
    change
      (FramedLatency.window outputs
        (start + FFTStage.latency geometry pipeline) (by omega) cycle)
          .o_data (Fin.cast (by rfl) physicalLane) = _
    rw [FramedLatency.window_apply, outputIndexEqual, ← finalAt,
      parentOutput]
    rw [outputFrameOfBankSignals_apply]
    change
      (if laneCoordinate.1 = 0 then
          castButterflyOutput configuration geometry
            ((finalStep.children (.lane lane)).outputs .o_upper)
        else
          castButterflyOutput configuration geometry
            ((finalStep.children (.lane lane)).outputs .o_lower)) =
        PipelinedFixedButterfly.encodeComplex
          (configuration.boundaryFormat geometry.stage.succ).width
          (if laneCoordinate.1 = 0 then
            (HTFFT.Butterfly.Fixed.butterfly
              (configuration.fixedConfig.butterfly geometry.stage)
              (PipelinedFixedButterfly.decodeComplex
                (dataFormat configuration geometry).width
                (bankFrameSignals configuration geometry bankState first data
                  continuation cycle lane).operands.a)
              (PipelinedFixedButterfly.decodeComplex
                (dataFormat configuration geometry).width
                (bankFrameSignals configuration geometry bankState first data
                  continuation cycle lane).operands.b)
              (table.value geometry.stage
                (twiddleAddress geometry
                  (bankFrameSignals configuration geometry bankState first data
                    continuation cycle lane).outputPhase lane))).upper
          else
            (HTFFT.Butterfly.Fixed.butterfly
              (configuration.fixedConfig.butterfly geometry.stage)
              (PipelinedFixedButterfly.decodeComplex
                (dataFormat configuration geometry).width
                (bankFrameSignals configuration geometry bankState first data
                  continuation cycle lane).operands.a)
              (PipelinedFixedButterfly.decodeComplex
                (dataFormat configuration geometry).width
                (bankFrameSignals configuration geometry bankState first data
                  continuation cycle lane).operands.b)
              (table.value geometry.stage
                (twiddleAddress geometry
                  (bankFrameSignals configuration geometry bankState first data
                    continuation cycle lane).outputPhase lane))).lower)
    rw [← visibleEqual']
    by_cases upper : laneCoordinate.1 = 0
    · rw [if_pos upper, if_pos upper, laneRelated.1]
      exact cast_encodeComplex configuration geometry _
    · rw [if_neg upper, if_neg upper, laneRelated.2]
      exact cast_encodeComplex configuration geometry _

end HTFFT.Silean.FFTStage.Internal
