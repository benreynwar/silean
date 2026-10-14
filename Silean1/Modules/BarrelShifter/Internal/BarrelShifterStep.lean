import Silean.Modules.BarrelShifter.Internal.BarrelShifterStructural

/-! One-cycle wiring equations for the complete barrel shifter. -/

namespace Silean.Modules.BarrelShifter.Internal

open Silean
open Silean.Modules

/-- A stage receives the parent payload at stage zero and the preceding
stage's payload thereafter. -/
theorem stageInput_of_solution
    {element : SignalType} {exponent : Nat} {pipeline : Pipeline exponent}
    {step : HierStep
      (Modules.BarrelShifter.moduleStructure element exponent pipeline)}
    (satisfies : (Modules.BarrelShifter.moduleStructure
      element exponent pipeline).IsSolution step)
    (stage : Fin exponent) :
    ((step.children (.stage stage)).inputs .shift,
      (step.children (.stage stage)).inputs .data) =
      if _zero : stage.val = 0 then
        (step.inputs .shift, step.inputs .data)
      else
        ((step.children (.stage (previousStage exponent stage))).outputs .shift,
          (step.children (.stage (previousStage exponent stage))).outputs .result) := by
  have shiftInput := ModuleStructure.child_input satisfies (.stage stage) .shift
  have dataInput := ModuleStructure.child_input satisfies (.stage stage) .data
  by_cases zero : stage.val = 0
  · simp only [Modules.BarrelShifter.wiring, dif_pos zero] at shiftInput dataInput
    simp [zero, shiftInput, dataInput]
  · simp only [Modules.BarrelShifter.wiring, dif_neg zero] at shiftInput dataInput
    simp [zero, shiftInput, dataInput]

/-- The final delay receives the parent data directly for an empty network,
and the last mux-stage result otherwise. -/
theorem outputDelayInput_of_solution
    {element : SignalType} {exponent : Nat} {pipeline : Pipeline exponent}
    {step : HierStep
      (Modules.BarrelShifter.moduleStructure element exponent pipeline)}
    (satisfies : (Modules.BarrelShifter.moduleStructure
      element exponent pipeline).IsSolution step) :
    (step.children .outputDelay).inputs .input =
      if empty : exponent = 0 then
        step.inputs .data
      else
        (step.children (.stage (lastStage exponent empty))).outputs .result := by
  have input := ModuleStructure.child_input satisfies .outputDelay .input
  by_cases empty : exponent = 0
  · simpa only [Modules.BarrelShifter.wiring, dif_pos empty,
      EndpointContext.moduleInput, SignalSource.value] using input
  · simpa only [Modules.BarrelShifter.wiring, dif_neg empty,
      EndpointContext.instanceOutput, SignalSource.value] using input

/-- The parent result is the final optional register's output. -/
theorem output_of_solution
    {element : SignalType} {exponent : Nat} {pipeline : Pipeline exponent}
    {step : HierStep
      (Modules.BarrelShifter.moduleStructure element exponent pipeline)}
    (satisfies : (Modules.BarrelShifter.moduleStructure
      element exponent pipeline).IsSolution step) :
    step.outputs .result = (step.children .outputDelay).outputs .output := by
  simpa only [Modules.BarrelShifter.wiring,
    EndpointContext.instanceOutput, SignalSource.value] using
      ModuleStructure.parent_output satisfies .result

end Silean.Modules.BarrelShifter.Internal
