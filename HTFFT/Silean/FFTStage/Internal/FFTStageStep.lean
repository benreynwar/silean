import HTFFT.Silean.FFTStage.Internal.FFTStageStructural

/-! One-cycle structural equations for the complete rolled FFT stage. -/

namespace HTFFT.Silean.FFTStage.Internal

open _root_.Silean
open _root_.Silean.Modules

variable {depth : Nat} {configuration : FFTConfiguration depth}
  {table : HTFFT.Fixed.TwiddleTable depth} {geometry : Geometry depth}
  {pipeline : PipelinedFixedButterfly.Pipeline}
  {twiddleDefinitionName : String}

private abbrev stageStructure
    (configuration : FFTConfiguration depth)
    (table : HTFFT.Fixed.TwiddleTable depth)
    (geometry : Geometry depth)
    (pipeline : PipelinedFixedButterfly.Pipeline)
    (twiddleDefinitionName : String) :=
  moduleStructure depth configuration table geometry pipeline
    twiddleDefinitionName

/-- The aggregate input splitter exposes the corresponding parent lane. -/
theorem inputSample_of_solution
    {step : HierStep (stageStructure configuration table geometry pipeline
      twiddleDefinitionName)}
    (satisfies : (stageStructure configuration table geometry pipeline
      twiddleDefinitionName).IsSolution step)
    (sample : Fin geometry.laneCount) :
    (step.children .inputSplit).outputs sample =
      step.inputs .i_data sample := by
  have splitInput := ModuleStructure.child_input satisfies .inputSplit .value
  change (step.children .inputSplit).inputs .value =
    step.inputs .i_data at splitInput
  have splitOutputs := ModuleStructure.splitter_outputs_of_solution
    (by simpa only [structuralChildren] using
      ModuleStructure.child_isSolution satisfies .inputSplit)
  calc
    (step.children .inputSplit).outputs sample =
        (inputSplitter configuration geometry).outputValues
          (step.children .inputSplit).inputs sample :=
      congrFun splitOutputs sample
    _ = (step.children .inputSplit).inputs .value sample := rfl
    _ = step.inputs .i_data sample := congrFun splitInput sample

/-- Shared control observes the parent marker directly. -/
theorem controlInput_of_solution
    {step : HierStep (stageStructure configuration table geometry pipeline
      twiddleDefinitionName)}
    (satisfies : (stageStructure configuration table geometry pipeline
      twiddleDefinitionName).IsSolution step) :
    (step.children .control).inputs .i_first = step.inputs .i_first := by
  exact ModuleStructure.child_input satisfies .control .i_first

/-- One physical lane observes shared control and the corresponding two input
branches. -/
theorem laneInputs_of_solution
    {step : HierStep (stageStructure configuration table geometry pipeline
      twiddleDefinitionName)}
    (satisfies : (stageStructure configuration table geometry pipeline
      twiddleDefinitionName).IsSolution step)
    (lane : Fin (butterflyCount geometry)) :
    (step.children (.lane lane)).inputs .i_firstHalf =
        (step.children .control).outputs .o_firstHalf ∧
      (step.children (.lane lane)).inputs .i_outputPhase =
        (step.children .control).outputs .o_outputPhase ∧
      (step.children (.lane lane)).inputs .i_branchA =
        step.inputs .i_data
          (geometry.inputBoundary.laneEquiv.symm (0, lane)) ∧
      (step.children (.lane lane)).inputs .i_branchB =
        step.inputs .i_data
          (geometry.inputBoundary.laneEquiv.symm (1, lane)) := by
  have firstHalf := ModuleStructure.child_input satisfies (.lane lane) .i_firstHalf
  have outputPhase := ModuleStructure.child_input satisfies (.lane lane) .i_outputPhase
  have branchA := ModuleStructure.child_input satisfies (.lane lane) .i_branchA
  have branchB := ModuleStructure.child_input satisfies (.lane lane) .i_branchB
  change (step.children (.lane lane)).inputs .i_firstHalf =
    (step.children .control).outputs .o_firstHalf at firstHalf
  change (step.children (.lane lane)).inputs .i_outputPhase =
    (step.children .control).outputs .o_outputPhase at outputPhase
  change (step.children (.lane lane)).inputs .i_branchA =
    (step.children .inputSplit).outputs
      (geometry.inputBoundary.laneEquiv.symm (0, lane)) at branchA
  change (step.children (.lane lane)).inputs .i_branchB =
    (step.children .inputSplit).outputs
      (geometry.inputBoundary.laneEquiv.symm (1, lane)) at branchB
  exact ⟨firstHalf, outputPhase,
    branchA.trans (inputSample_of_solution satisfies _),
    branchB.trans (inputSample_of_solution satisfies _)⟩

/-- A parent output lane is the selected upper or lower branch of its owning
physical butterfly lane. -/
theorem outputSample_of_solution
    {step : HierStep (stageStructure configuration table geometry pipeline
      twiddleDefinitionName)}
    (satisfies : (stageStructure configuration table geometry pipeline
      twiddleDefinitionName).IsSolution step)
    (sample : Fin geometry.laneCount) :
    step.outputs .o_data sample =
      let branchLane := geometry.outputBoundary.laneEquiv sample
      if branchLane.1 = 0 then
        castButterflyOutput configuration geometry
          ((step.children (.lane branchLane.2)).outputs .o_upper)
      else
        castButterflyOutput configuration geometry
          ((step.children (.lane branchLane.2)).outputs .o_lower) := by
  have parentOutput := ModuleStructure.parent_output satisfies .o_data
  change step.outputs .o_data =
    (step.children .outputCombine).outputs .value at parentOutput
  have combineOutputs := ModuleStructure.combiner_outputs_of_solution
    (by simpa only [structuralChildren] using
      ModuleStructure.child_isSolution satisfies .outputCombine)
  have combineAt : (step.children .outputCombine).outputs .value sample =
      (step.children .outputCombine).inputs sample := by
    exact congrFun (congrFun combineOutputs .value) sample
  have combineInput := ModuleStructure.child_input satisfies .outputCombine sample
  by_cases upper : (geometry.outputBoundary.laneEquiv sample).1 = 0
  · simp only [wiring, upper, if_true,
      SignalSource.value_castType, EndpointContext.instanceOutput_value]
      at combineInput
    rw [castTypeValue_eq_castButterflyOutput] at combineInput
    calc
      step.outputs .o_data sample =
          (step.children .outputCombine).outputs .value sample :=
        congrFun parentOutput sample
      _ = (step.children .outputCombine).inputs sample := combineAt
      _ = castButterflyOutput configuration geometry
          ((step.children (.lane
            (geometry.outputBoundary.laneEquiv sample).2)).outputs .o_upper) :=
        combineInput
      _ = _ := by simp only [upper, if_pos]
  · simp only [wiring, upper, if_false,
      SignalSource.value_castType, EndpointContext.instanceOutput_value]
      at combineInput
    rw [castTypeValue_eq_castButterflyOutput] at combineInput
    calc
      step.outputs .o_data sample =
          (step.children .outputCombine).outputs .value sample :=
        congrFun parentOutput sample
      _ = (step.children .outputCombine).inputs sample := combineAt
      _ = castButterflyOutput configuration geometry
          ((step.children (.lane
            (geometry.outputBoundary.laneEquiv sample).2)).outputs .o_lower) :=
        combineInput
      _ = _ := by
        rw [if_neg]
        exact upper

/-- Boundary-indexed form of `outputSample_of_solution`.  This avoids making
clients unfold the definitionally equal input and output lane counts. -/
theorem outputBoundarySample_of_solution
    {step : HierStep (stageStructure configuration table geometry pipeline
      twiddleDefinitionName)}
    (satisfies : (stageStructure configuration table geometry pipeline
      twiddleDefinitionName).IsSolution step)
    (sample : Fin geometry.outputBoundary.laneCount) :
    step.outputs .o_data (Fin.cast (by rfl) sample) =
      let branchLane := geometry.outputBoundary.laneEquiv sample
      let lane : Fin (butterflyCount geometry) :=
        Fin.cast (by rfl) branchLane.2
      if branchLane.1 = 0 then
        castButterflyOutput configuration geometry
          ((step.children (.lane lane)).outputs .o_upper)
      else
        castButterflyOutput configuration geometry
          ((step.children (.lane lane)).outputs .o_lower) := by
  exact outputSample_of_solution satisfies (Fin.cast (by rfl) sample)

/-- Marker alignment is a direct serial path from control to the boundary. -/
theorem markerWiring_of_solution
    {step : HierStep (stageStructure configuration table geometry pipeline
      twiddleDefinitionName)}
    (satisfies : (stageStructure configuration table geometry pipeline
      twiddleDefinitionName).IsSolution step) :
    (step.children .markerAlign).inputs .input =
        (step.children .control).outputs .o_delayedFirst ∧
      step.outputs .o_first =
        (step.children .markerAlign).outputs .output := by
  exact ⟨ModuleStructure.child_input satisfies .markerAlign .input,
    ModuleStructure.parent_output satisfies .o_first⟩

end HTFFT.Silean.FFTStage.Internal
