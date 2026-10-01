import Silean.Modules.BarrelShifter.Internal.BarrelShifterLevelStructural

/-! Behavioral theorem for one combinational barrel-shifter level. -/

namespace Silean.Modules.BarrelShifter.Internal.Level

open Silean
open Silean.Modules

/-- Every realizable level step has the natural conditional-rotation result. -/
theorem result_of_realization (element : SignalType) (exponent : Nat)
    (stage : Fin exponent)
    {step : (BarrelShifterLevel.moduleStructure element exponent stage).Step}
    (realizes :
      (BarrelShifterLevel.moduleStructure element exponent stage).Realizes step) :
    step.outputs .result =
      resultValue exponent stage (step.inputs .shift) (step.inputs .data) := by
  obtain ⟨hierStep, satisfies, stepEqual⟩ := realizes
  subst step

  have shiftInput := ModuleStructure.child_input satisfies .shiftSplit .value
  have rotateInput := ModuleStructure.child_input satisfies .rotate .input
  have selectBit := ModuleStructure.child_input satisfies .select .select
  have falseInput := ModuleStructure.child_input satisfies .select .whenFalse
  have trueInput := ModuleStructure.child_input satisfies .select .whenTrue
  have parentOutput := ModuleStructure.parent_output satisfies .result

  have splitSolution := ModuleStructure.child_isSolution satisfies .shiftSplit
  have splitOutputs : (hierStep.children .shiftSplit).outputs =
      (shiftSplitter exponent).outputValues
        (hierStep.children .shiftSplit).inputs :=
    ModuleStructure.splitter_outputs_of_solution (by
      simpa only [BarrelShifterLevel.structuralChildren] using splitSolution)
  have splitAt : (hierStep.children .shiftSplit).outputs stage =
      (hierStep.children .shiftSplit).inputs .value stage := by
    exact congrFun splitOutputs stage

  have rotateRealizes := ModuleStructure.child_realizes satisfies .rotate
  have rotateOutput := VectorReindex.output_of_realization element
    (BarrelShifter.size exponent) (BarrelShifter.size exponent)
    (sourceIndex exponent stage) (by
      simpa only [BarrelShifterLevel.structuralChildren] using rotateRealizes)

  have selectRealizes := ModuleStructure.child_realizes satisfies .select
  have selectOutput := Mux.result_of_realization
    (.vector (BarrelShifter.size exponent) element) (by
      simpa only [BarrelShifterLevel.structuralChildren] using selectRealizes)

  change (hierStep.children .shiftSplit).inputs .value =
    hierStep.inputs .shift at shiftInput
  change (hierStep.children .rotate).inputs .input =
    hierStep.inputs .data at rotateInput
  change (hierStep.children .select).inputs .select =
    (hierStep.children .shiftSplit).outputs stage at selectBit
  change (hierStep.children .select).inputs .whenFalse =
    hierStep.inputs .data at falseInput
  change (hierStep.children .select).inputs .whenTrue =
    (hierStep.children .rotate).outputs .output at trueInput
  change hierStep.outputs .result =
    (hierStep.children .select).outputs .result at parentOutput
  change (hierStep.children .rotate).outputs .output =
    VectorReindex.apply (sourceIndex exponent stage)
      ((hierStep.children .rotate).inputs .input) at rotateOutput
  change (hierStep.children .select).outputs .result =
    bif (hierStep.children .select).inputs .select then
      (hierStep.children .select).inputs .whenTrue
    else (hierStep.children .select).inputs .whenFalse at selectOutput

  change hierStep.outputs .result =
    resultValue exponent stage (hierStep.inputs .shift) (hierStep.inputs .data)
  rw [parentOutput, selectOutput, selectBit, splitAt, shiftInput,
    falseInput, trueInput, rotateOutput, rotateInput]
  rfl

end Silean.Modules.BarrelShifter.Internal.Level
