import HTFFT.Silean.FFT.FFTStageChain
import HTFFT.Silean.FFTStage.FFTStage
import Silean.Authoring.ModuleDesign

/-! Permanent rolled-stage chain body with unresolved stage children. -/

namespace HTFFT.Silean.FFT.FFTStageChain.Internal

open _root_.Silean

/-- The preceding rolled-stage index of a noninitial family member. -/
def previousIndex (configuration : Configuration depth)
    (index : StageIndex configuration) (nonzero : index.val ≠ 0) :
    StageIndex configuration :=
  ⟨index.val - 1, by
    have positive := Nat.pos_of_ne_zero nonzero
    omega⟩

/-- The following rolled-stage index when another family member remains. -/
def nextIndex (configuration : Configuration depth)
    (index : StageIndex configuration)
    (hasNext : index.val + 1 < stageCount depth configuration) :
    StageIndex configuration :=
  ⟨index.val + 1, hasNext⟩

@[simp] theorem previousIndex_nextIndex
    (configuration : Configuration depth)
    (index : StageIndex configuration)
    (hasNext : index.val + 1 < stageCount depth configuration) :
    previousIndex configuration (nextIndex configuration index hasNext)
        (by simp [nextIndex]) = index := by
  apply Fin.ext
  simp [previousIndex, nextIndex]

/-- Advancing the family index advances the public stage geometry once. -/
theorem stageGeometry_nextIndex
    (configuration : Configuration depth)
    (index : StageIndex configuration)
    (hasNext : index.val + 1 < stageCount depth configuration) :
    stageGeometry configuration (nextIndex configuration index hasNext) =
      (stageGeometry configuration index).next (by
        have laneLe := configuration.laneDepth_le_depth
        have nextLt := hasNext
        simp only [stageCount] at nextLt
        simp only [stageGeometry_stage_val]
        omega) := by
  apply FFTStage.Geometry.ext
  · rfl
  · apply Fin.ext
    rfl

/-- The final rolled-stage index when the rolled suffix is nonempty. -/
def lastIndex (configuration : Configuration depth)
    (nonempty : depth - configuration.laneDepth ≠ 0) :
    StageIndex configuration :=
  ⟨depth - configuration.laneDepth - 1, by
    change depth - configuration.laneDepth - 1 <
      depth - configuration.laneDepth
    exact Nat.sub_one_lt nonempty⟩

private theorem firstStage_eq
    (configuration : Configuration depth)
    (index : StageIndex configuration) (zero : index.val = 0) :
    index = ⟨0, by omega⟩ := by
  apply Fin.ext
  exact zero

/-- The first rolled stage consumes the chain's prefix boundary layout. -/
theorem firstStage_inputBoundary
    (configuration : Configuration depth)
    (index : StageIndex configuration) (zero : index.val = 0) :
    (stageGeometry configuration index).inputBoundary =
      configuration.prefixGeometry := by
  rw [firstStage_eq configuration index zero]
  rfl

/-- The output layout of a stage is the input layout of its successor in the
rolled family. -/
theorem previousStage_outputBoundary
    (configuration : Configuration depth)
    (index : StageIndex configuration) (nonzero : index.val ≠ 0) :
    (stageGeometry configuration
        (previousIndex configuration index nonzero)).outputBoundary =
      (stageGeometry configuration index).inputBoundary := by
  apply FFTStage.BoundaryGeometry.ext
  · rfl
  · apply Fin.ext
    change configuration.laneDepth + (index.val - 1) + 1 =
      configuration.laneDepth + index.val
    omega

/-- A noninitial indexed geometry is precisely the successor of its
predecessor's geometry. -/
theorem previousStage_nextGeometry
    (configuration : Configuration depth)
    (index : StageIndex configuration) (nonzero : index.val ≠ 0) :
    (stageGeometry configuration
        (previousIndex configuration index nonzero)).next (by
          simp only [stageGeometry_stage_val, previousIndex]
          have indexLt := index.isLt
          have laneLe := configuration.laneDepth_le_depth
          simp only [stageCount] at indexLt
          omega) =
      stageGeometry configuration index := by
  apply FFTStage.Geometry.ext
  · rfl
  · apply Fin.ext
    change configuration.laneDepth + (index.val - 1) + 1 =
      configuration.laneDepth + index.val
    omega

/-- The last rolled stage produces the chain's final physical layout. -/
theorem lastStage_outputBoundary
    (configuration : Configuration depth)
    (nonempty : depth - configuration.laneDepth ≠ 0) :
    (stageGeometry configuration
        (lastIndex configuration nonempty)).outputBoundary =
      configuration.finalGeometry := by
  apply FFTStage.BoundaryGeometry.ext
  · rfl
  · apply Fin.ext
    change configuration.laneDepth +
        (depth - configuration.laneDepth - 1) + 1 = depth
    have laneLe := configuration.laneDepth_le_depth
    omega

/-- With no rolled stages, the prefix boundary is already final. -/
theorem prefixGeometry_eq_finalGeometry_of_empty
    (configuration : Configuration depth)
    (empty : depth - configuration.laneDepth = 0) :
    configuration.prefixGeometry = configuration.finalGeometry := by
  apply FFTStage.BoundaryGeometry.ext
  · rfl
  · apply Fin.ext
    change configuration.laneDepth = depth
    have laneLe := configuration.laneDepth_le_depth
    omega

/-- The chain input has exactly the data shape consumed by its first rolled
stage. -/
theorem parentInputType_eq_stageInputType
    (configuration : Configuration depth)
    (index : StageIndex configuration) (zero : index.val = 0) :
    (FFTStageChain.ports configuration).inputs.signalType
        FFTStageChain.Input.i_data =
      (FFTStage.ports configuration.arithmetic
        (stageGeometry configuration index)).inputs.signalType
          FFTStage.Input.i_data := by
  apply congrArg (fun format =>
    SignalType.vector configuration.laneCount
      (FFTStage.complexSignalType format))
  apply congrArg configuration.arithmetic.boundaryFormat
  apply Fin.ext
  simp [stageGeometry, zero]

/-- Carrier-level form of `parentInputType_eq_stageInputType`. -/
theorem parentInputData_eq_stageInputData
    (configuration : Configuration depth)
    (index : StageIndex configuration) (zero : index.val = 0) :
    PrefixData configuration =
      FFTStage.InputData configuration.arithmetic
        (stageGeometry configuration index) := by
  change FFTStage.BoundaryData configuration.arithmetic
      configuration.prefixGeometry =
    FFTStage.BoundaryData configuration.arithmetic
      (stageGeometry configuration index).inputBoundary
  exact congrArg (FFTStage.BoundaryData configuration.arithmetic)
    (firstStage_inputBoundary configuration index zero).symm

/-- Observation-level form of `parentInputData_eq_stageInputData`. -/
theorem parentInputObservation_eq_stageInputObservation
    (configuration : Configuration depth)
    (index : StageIndex configuration) (zero : index.val = 0) :
    FFTStageChain.InputObservation configuration =
      FFTStage.InputObservation configuration.arithmetic
        (stageGeometry configuration index) :=
  congrArg (fun data => Bool × data)
    (parentInputData_eq_stageInputData configuration index zero)

/-- Consecutive rolled stages expose identical packed data shapes at their
shared boundary. -/
theorem previousOutputType_eq_stageInputType
    (configuration : Configuration depth)
    (index : StageIndex configuration) (nonzero : index.val ≠ 0) :
    (FFTStage.ports configuration.arithmetic
        (stageGeometry configuration (previousIndex configuration index nonzero))).outputs.signalType
          FFTStage.Output.o_data =
      (FFTStage.ports configuration.arithmetic
        (stageGeometry configuration index)).inputs.signalType
          FFTStage.Input.i_data := by
  apply congrArg (fun format =>
    SignalType.vector configuration.laneCount
      (FFTStage.complexSignalType format))
  apply congrArg configuration.arithmetic.boundaryFormat
  apply Fin.ext
  simp [stageGeometry, previousIndex]
  omega

/-- Carrier-level form of the shared boundary between consecutive rolled
stages. -/
theorem previousOutputData_eq_stageInputData
    (configuration : Configuration depth)
    (index : StageIndex configuration) (nonzero : index.val ≠ 0) :
    FFTStage.OutputData configuration.arithmetic
        (stageGeometry configuration
          (previousIndex configuration index nonzero)) =
      FFTStage.InputData configuration.arithmetic
        (stageGeometry configuration index) :=
  congrArg (FFTStage.BoundaryData configuration.arithmetic)
    (previousStage_outputBoundary configuration index nonzero)

/-- Observation-level form of the shared boundary between consecutive rolled
stages. -/
theorem previousOutputObservation_eq_stageInputObservation
    (configuration : Configuration depth)
    (index : StageIndex configuration) (nonzero : index.val ≠ 0) :
    FFTStage.OutputObservation configuration.arithmetic
        (stageGeometry configuration
          (previousIndex configuration index nonzero)) =
      FFTStage.InputObservation configuration.arithmetic
        (stageGeometry configuration index) :=
  congrArg (fun data => Bool × data)
    (previousOutputData_eq_stageInputData configuration index nonzero)

/-- The final rolled stage has exactly the chain's output data shape. -/
theorem lastOutputType_eq_parentOutputType
    (configuration : Configuration depth)
    (nonempty : depth - configuration.laneDepth ≠ 0) :
    (FFTStage.ports configuration.arithmetic
        (stageGeometry configuration (lastIndex configuration nonempty))).outputs.signalType
          FFTStage.Output.o_data =
      (FFTStageChain.ports configuration).outputs.signalType
        FFTStageChain.Output.o_data := by
  apply congrArg (fun format =>
    SignalType.vector configuration.laneCount
      (FFTStage.complexSignalType format))
  apply congrArg configuration.arithmetic.boundaryFormat
  apply Fin.ext
  simp [stageGeometry, lastIndex]
  have laneLe := configuration.laneDepth_le_depth
  omega

/-- Carrier-level form of the final rolled-stage boundary. -/
theorem lastOutputData_eq_parentOutputData
    (configuration : Configuration depth)
    (nonempty : depth - configuration.laneDepth ≠ 0) :
    FFTStage.OutputData configuration.arithmetic
        (stageGeometry configuration (lastIndex configuration nonempty)) =
      OutputData configuration := by
  change FFTStage.BoundaryData configuration.arithmetic
      (stageGeometry configuration
        (lastIndex configuration nonempty)).outputBoundary =
    FFTStage.BoundaryData configuration.arithmetic
      configuration.finalGeometry
  exact congrArg (FFTStage.BoundaryData configuration.arithmetic)
    (lastStage_outputBoundary configuration nonempty)

/-- Observation-level form of the final rolled-stage boundary. -/
theorem lastOutputObservation_eq_parentOutputObservation
    (configuration : Configuration depth)
    (nonempty : depth - configuration.laneDepth ≠ 0) :
    FFTStage.OutputObservation configuration.arithmetic
        (stageGeometry configuration (lastIndex configuration nonempty)) =
      FFTStageChain.OutputObservation configuration :=
  congrArg (fun data => Bool × data)
    (lastOutputData_eq_parentOutputData configuration nonempty)

/-- With no rolled stages, the prefix and final packed data shapes coincide. -/
theorem parentInputType_eq_parentOutputType_of_empty
    (configuration : Configuration depth)
    (empty : depth - configuration.laneDepth = 0) :
    (FFTStageChain.ports configuration).inputs.signalType
        FFTStageChain.Input.i_data =
      (FFTStageChain.ports configuration).outputs.signalType
        FFTStageChain.Output.o_data := by
  apply congrArg (fun format =>
    SignalType.vector configuration.laneCount
      (FFTStage.complexSignalType format))
  apply congrArg configuration.arithmetic.boundaryFormat
  apply Fin.ext
  have laneLe := configuration.laneDepth_le_depth
  simp
  omega

/-- Carrier-level form of the empty chain boundary. -/
theorem parentInputData_eq_parentOutputData_of_empty
    (configuration : Configuration depth)
    (empty : depth - configuration.laneDepth = 0) :
    PrefixData configuration =
      OutputData configuration := by
  change FFTStage.BoundaryData configuration.arithmetic
      configuration.prefixGeometry =
    FFTStage.BoundaryData configuration.arithmetic
      configuration.finalGeometry
  exact congrArg (FFTStage.BoundaryData configuration.arithmetic)
    (prefixGeometry_eq_finalGeometry_of_empty configuration empty)

/-- Observation-level form of the empty chain boundary. -/
theorem parentInputObservation_eq_parentOutputObservation_of_empty
    (configuration : Configuration depth)
    (empty : depth - configuration.laneDepth = 0) :
    FFTStageChain.InputObservation configuration =
      FFTStageChain.OutputObservation configuration :=
  congrArg (fun data => Bool × data)
    (parentInputData_eq_parentOutputData_of_empty configuration empty)

end HTFFT.Silean.FFT.FFTStageChain.Internal

namespace HTFFT.Silean.FFT

open _root_.Silean
open _root_.Silean.Authoring

module_design FFTStageChain
    (depth : Nat) (configuration : FFT.Configuration depth)
    (table : HTFFT.Fixed.TwiddleTable depth) where
  boundary (FFTStageChain.ports configuration)
    (naming := FFTStageChain.Naming.ports configuration)
  instances {
    stage
        (index : Fin (FFTStageChain.stageCount depth configuration) in
          Enumeration.fin (FFTStageChain.stageCount depth configuration))
        (name := .indexed "stage" index.val) := unresolved (
      FFTStage.ports configuration.arithmetic
        (FFTStageChain.stageGeometry configuration index)) }
  wiring {
    outputs {
      .o_first := from (
        let context := FFTStageChain.context depth configuration table
        if empty : depth - configuration.laneDepth = 0 then
          context.moduleInput .i_first
        else
          context.instanceOutput
            (.stage (FFTStageChain.Internal.lastIndex configuration empty))
            .o_first),
      .o_data := from (
        let context := FFTStageChain.context depth configuration table
        if empty : depth - configuration.laneDepth = 0 then
          SignalSource.castType
            (FFTStageChain.Internal.parentInputType_eq_parentOutputType_of_empty
              configuration empty)
            (context.moduleInput .i_data)
        else
          SignalSource.castType
            (FFTStageChain.Internal.lastOutputType_eq_parentOutputType
              configuration empty)
            (context.instanceOutput
              (.stage (FFTStageChain.Internal.lastIndex configuration empty))
              .o_data)) }
    instance (.stage index) {
      .i_first := from (
        let context := FFTStageChain.context depth configuration table
        if zero : index.val = 0 then
          context.moduleInput .i_first
        else
          context.instanceOutput
            (.stage
              (FFTStageChain.Internal.previousIndex configuration index zero))
            .o_first),
      .i_data := from (
        let context := FFTStageChain.context depth configuration table
        if zero : index.val = 0 then
          SignalSource.castType
            (FFTStageChain.Internal.parentInputType_eq_stageInputType
              configuration index zero)
            (context.moduleInput .i_data)
        else
          SignalSource.castType
            (FFTStageChain.Internal.previousOutputType_eq_stageInputType
              configuration index zero)
            (context.instanceOutput
              (.stage
                (FFTStageChain.Internal.previousIndex configuration index zero))
              .o_data)) }
  }

end HTFFT.Silean.FFT
