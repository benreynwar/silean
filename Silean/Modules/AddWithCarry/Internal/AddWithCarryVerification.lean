import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Modules.AddWithCarry.Internal.AddWithCarryArithmetic
import Silean.Modules.AddWithCarry.Internal.AddWithCarryStructure
import Silean.Modules.Constant.Constant
import Silean.Modules.FullAdder.FullAdderDerived
import Silean.Modules.VectorConcat.VectorConcatDerived

/-! Internal schedules and inductive certification for the recursive adder. -/

namespace Silean.Modules.AddWithCarry

open Silean
open Contracts.Cycle.Certification.Layer
open Internal

private abbrev Implementation (width : Nat) :=
  Contracts.Cycle.ModuleCycleCertification (moduleStructure width) (cycleContract width)

private def Implementation.certified (implementation : Implementation width) :
    Contracts.Cycle.ModuleCycleCertified (ports width) := implementation.bundle

@[reducible] private def baseChildContracts : Contracts.Cycle.ChildCycleContracts baseBody
  | .empty => Modules.Constant.cycleContract (.vector 0 .bit) emptyValue

private abbrev baseOccurrence :
    RuleOccurrence baseBody baseChildContracts :=
  ⟨.empty, Primitives.ConstantRule.apply⟩

private def baseScheduleOrders : ScheduleDerivation.RuleScheduleOrders
    baseBody baseChildContracts (cycleContract 0) where
  output | .apply => [baseOccurrence]
  state := []

private def baseDerivedRuleSchedules : ScheduleDerivation.DerivedRuleSchedules
    baseBody baseChildContracts (cycleContract 0) := by
  derive_rule_schedules baseScheduleOrders

private abbrev baseSchedules := baseDerivedRuleSchedules.schedules

private theorem baseCoversChildren : baseSchedules.CoversChildren :=
  baseDerivedRuleSchedules.coversChildren

private theorem baseImplements
    (layerChildren : ChildStructures baseBody baseChildContracts) :
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure baseBody layerChildren)
      (cycleContract 0) (fun _ _ => True) := by
  intro contractState hierStep corresponds satisfies
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [applyRule_holds_iff]
    dsimp only
    constructor
    · funext index
      exact Fin.elim0 index
    · rw [show hierStep.outputs .carryOut = hierStep.inputs .carryIn by
          exact boundary .carryOut]
      cases hierStep.inputs .carryIn <;>
        simp [carryValue, totalValue, BitVector.toNat]
  · rfl

private noncomputable opaque baseCertifiedLayer :
    Contracts.Cycle.ModuleCycleCertifiedLayer baseBody baseChildContracts
      (cycleContract 0) :=
  RuleSchedules.certifiedLayer baseSchedules baseCoversChildren
    (fun _ _ _ => True) (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩)
    baseImplements

private noncomputable def baseCertifiedChildren :
    ChildStructures baseBody baseChildContracts
  | .empty => (Modules.Constant.certified (.vector 0 .bit) emptyValue).certifiedStructure

private noncomputable def baseImplementation : Implementation 0 :=
  (baseCertifiedLayer.certify baseCertifiedChildren).transportStructure (by rfl)

@[reducible] private def succChildContracts (width : Nat) :
    Contracts.Cycle.ChildCycleContracts (succBody width)
  | .leftSplit => (operandSplitter width).cycleContract
  | .rightSplit => (operandSplitter width).cycleContract
  | .lowerLeft => (lowerCombiner width).cycleContract
  | .lowerRight => (lowerCombiner width).cycleContract
  | .lowerAdd => cycleContract width
  | .highAdder => FullAdder.cycleContract
  | .highBit => highCombiner.cycleContract
  | .concat => VectorConcat.cycleContract .bit width 1

private abbrev leftSplitOccurrence (width) :
    RuleOccurrence (succBody width) (succChildContracts width) :=
  ⟨.leftSplit, Composition.SignalComponentRule.apply⟩
private abbrev rightSplitOccurrence (width) :
    RuleOccurrence (succBody width) (succChildContracts width) :=
  ⟨.rightSplit, Composition.SignalComponentRule.apply⟩
private abbrev lowerLeftOccurrence (width) :
    RuleOccurrence (succBody width) (succChildContracts width) :=
  ⟨.lowerLeft, Composition.SignalComponentRule.apply⟩
private abbrev lowerRightOccurrence (width) :
    RuleOccurrence (succBody width) (succChildContracts width) :=
  ⟨.lowerRight, Composition.SignalComponentRule.apply⟩
private abbrev lowerAddOccurrence (width) :
    RuleOccurrence (succBody width) (succChildContracts width) :=
  ⟨.lowerAdd, Rule.apply⟩
private abbrev highSumOccurrence (width) :
    RuleOccurrence (succBody width) (succChildContracts width) :=
  ⟨.highAdder, FullAdder.Rule.sum⟩
private abbrev highCarryOccurrence (width) :
    RuleOccurrence (succBody width) (succChildContracts width) :=
  ⟨.highAdder, FullAdder.Rule.carryOut⟩
private abbrev highBitOccurrence (width) :
    RuleOccurrence (succBody width) (succChildContracts width) :=
  ⟨.highBit, Composition.SignalComponentRule.apply⟩
private abbrev concatOccurrence (width) :
    RuleOccurrence (succBody width) (succChildContracts width) :=
  ⟨.concat, VectorConcat.Rule.apply⟩

private def succScheduleOrders (width : Nat) :
    ScheduleDerivation.RuleScheduleOrders (succBody width)
      (succChildContracts width) (cycleContract (width + 1)) where
  output := fun
    | .apply => [leftSplitOccurrence width, lowerLeftOccurrence width,
        rightSplitOccurrence width, lowerRightOccurrence width,
        lowerAddOccurrence width, highSumOccurrence width,
        highCarryOccurrence width, highBitOccurrence width,
        concatOccurrence width]
  state := []

private def succDerivedRuleSchedules (width : Nat) :
    ScheduleDerivation.DerivedRuleSchedules (succBody width)
      (succChildContracts width) (cycleContract (width + 1)) := by
  derive_rule_schedules (succScheduleOrders width)

private abbrev succSchedules (width : Nat) :=
  (succDerivedRuleSchedules width).schedules

private theorem succCoversChildren (width : Nat) :
    (succSchedules width).CoversChildren :=
  (succDerivedRuleSchedules width).coversChildren

private def leftSplitInputs (width : Nat)
    (inputs : (ports (width + 1)).inputs.Values) :
    (operandSplitter width).ports.inputs.Values
  | .value => inputs .left

private def rightSplitInputs (width : Nat)
    (inputs : (ports (width + 1)).inputs.Values) :
    (operandSplitter width).ports.inputs.Values
  | .value => inputs .right

private def lowerLeftInputs (width : Nat)
    (split : (operandSplitter width).ports.outputs.Values) :
    (lowerCombiner width).ports.inputs.Values := fun index => split index.castSucc

private def lowerRightInputs (width : Nat)
    (split : (operandSplitter width).ports.outputs.Values) :
    (lowerCombiner width).ports.inputs.Values := fun index => split index.castSucc

private def lowerAddInputs (width : Nat)
    (inputs : (ports (width + 1)).inputs.Values)
    (lowerLeft lowerRight : (lowerCombiner width).ports.outputs.Values) :
    (ports width).inputs.Values
  | .left => lowerLeft .value
  | .right => lowerRight .value
  | .carryIn => inputs .carryIn

private def highAdderInputs (width : Nat)
    (leftSplit rightSplit : (operandSplitter width).ports.outputs.Values)
    (lower : (ports width).outputs.Values) : FullAdder.ports.inputs.Values
  | .left => leftSplit (highIndex width)
  | .right => rightSplit (highIndex width)
  | .carryIn => lower .carryOut

private def highBitInputs (adder : FullAdder.ports.outputs.Values) :
    highCombiner.ports.inputs.Values := fun _ => adder .sum

private def concatInputs (width : Nat)
    (lower : (ports width).outputs.Values)
    (highBit : highCombiner.ports.outputs.Values) :
    (VectorConcat.ports .bit width 1).inputs.Values
  | .left => lower .result
  | .right => highBit .value

private theorem concat_single_eq_lastCases (lower : Fin width → Bool)
    (high : Bool) :
    VectorConcat.concat lower (fun _ : Fin 1 => high) =
      Fin.lastCases high lower := by
  funext index
  refine Fin.lastCases ?_ (fun lowerIndex => ?_) index
  · have left : VectorConcat.concat lower (fun _ : Fin 1 => high)
        (Fin.last width) = high := by
      rw [show Fin.last width = Fin.natAdd width (0 : Fin 1) by
        apply Fin.ext; simp]
      exact VectorConcat.concat_right lower (fun _ : Fin 1 => high) 0
    simpa using left
  · have left : VectorConcat.concat lower (fun _ : Fin 1 => high)
        lowerIndex.castSucc = lower lowerIndex := by
      rw [show lowerIndex.castSucc = Fin.castAdd 1 lowerIndex by
        apply Fin.ext; rfl]
      exact VectorConcat.concat_left lower (fun _ : Fin 1 => high) lowerIndex
    simpa using left

private theorem succImplements (width : Nat)
    (layerChildren : ChildStructures (succBody width) (succChildContracts width)) :
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (succBody width) layerChildren)
      (cycleContract (width + 1)) (fun _ _ => True) := by
  intro contractState hierStep corresponds satisfies
  have boundary := satisfies.1
  have childStates : ∀ child, (succChildContracts width child).state.Values := by
    intro child
    cases child <;> exact SignalMap.emptyValues
  have childStateSubsingleton : ∀ child,
      Subsingleton (succChildContracts width child).state.Values := by
    intro child
    cases child <;> change Subsingleton emptySignalMap.Values <;> infer_instance
  have childMatches := childSolutionsMatchContracts_of_subsingletonState
    (body := succBody width) layerChildren hierStep satisfies childStates
      childStateSubsingleton
  have leftSplitOutputs : (hierStep.children .leftSplit).outputs =
      (operandSplitter width).outputValues
        (leftSplitInputs width hierStep.inputs) := by
    have holds := (Composition.SignalSplitter.outputRule_holds_iff
      (operandSplitter width) _ _ _).mp
      ((childMatches .leftSplit).ruleHolds Composition.SignalComponentRule.apply)
    have inputsEqual : (succBody width).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .leftSplit =
          leftSplitInputs width hierStep.inputs := by
      funext port
      cases port
      rfl
    rw [inputsEqual] at holds
    exact holds
  have rightSplitOutputs : (hierStep.children .rightSplit).outputs =
      (operandSplitter width).outputValues
        (rightSplitInputs width hierStep.inputs) := by
    have holds := (Composition.SignalSplitter.outputRule_holds_iff
      (operandSplitter width) _ _ _).mp
      ((childMatches .rightSplit).ruleHolds Composition.SignalComponentRule.apply)
    have inputsEqual : (succBody width).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .rightSplit =
          rightSplitInputs width hierStep.inputs := by
      funext port
      cases port
      rfl
    rw [inputsEqual] at holds
    exact holds
  have lowerLeftOutputs : (hierStep.children .lowerLeft).outputs =
      (lowerCombiner width).outputValues
        ((succBody width).wiring.childInputValues
          hierStep.inputs hierStep.childOutputs .lowerLeft) :=
    (Composition.SignalCombiner.outputRule_holds_iff
      (lowerCombiner width) _ _ _).mp
      ((childMatches .lowerLeft).ruleHolds Composition.SignalComponentRule.apply)
  have lowerRightOutputs : (hierStep.children .lowerRight).outputs =
      (lowerCombiner width).outputValues
        ((succBody width).wiring.childInputValues
          hierStep.inputs hierStep.childOutputs .lowerRight) :=
    (Composition.SignalCombiner.outputRule_holds_iff
      (lowerCombiner width) _ _ _).mp
      ((childMatches .lowerRight).ruleHolds Composition.SignalComponentRule.apply)
  have highBitOutputs : (hierStep.children .highBit).outputs =
      highCombiner.outputValues ((succBody width).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .highBit) :=
    (Composition.SignalCombiner.outputRule_holds_iff highCombiner _ _ _).mp
      ((childMatches .highBit).ruleHolds Composition.SignalComponentRule.apply)
  have lowerResultEquation :=
    (childMatches .lowerAdd).boundaryOutput
      (cycleContract.resultEquation width)
  have lowerCarryEquation :=
    (childMatches .lowerAdd).boundaryOutput
      (cycleContract.carryOutEquation width)
  have sumEquation :=
    (childMatches .highAdder).boundaryOutput
      FullAdder.cycleContract.sumEquation
  have carryEquation :=
    (childMatches .highAdder).boundaryOutput
      FullAdder.cycleContract.carryOutEquation
  have concatEquation := VectorConcat.cycleContract.result .bit width 1
    (childMatches .concat).allowed
  change (hierStep.children .concat).outputs .result =
    VectorConcat.concat
      ((succBody width).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .concat .left)
      ((succBody width).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .concat .right) at concatEquation
  have lowerLeftInputsEquation : (succBody width).wiring.childInputValues
      hierStep.inputs hierStep.childOutputs .lowerLeft =
        lowerLeftInputs width (hierStep.children .leftSplit).outputs := by
    funext index; rfl
  have lowerRightInputsEquation : (succBody width).wiring.childInputValues
      hierStep.inputs hierStep.childOutputs .lowerRight =
        lowerRightInputs width (hierStep.children .rightSplit).outputs := by
    funext index; rfl
  have lowerAddInputsEquation : (succBody width).wiring.childInputValues
      hierStep.inputs hierStep.childOutputs .lowerAdd =
        lowerAddInputs width hierStep.inputs
          (hierStep.children .lowerLeft).outputs
          (hierStep.children .lowerRight).outputs := by
    funext port; cases port <;> rfl
  have highAdderInputsEquation : (succBody width).wiring.childInputValues
      hierStep.inputs hierStep.childOutputs .highAdder =
        highAdderInputs width (hierStep.children .leftSplit).outputs
          (hierStep.children .rightSplit).outputs
          (hierStep.children .lowerAdd).outputs := by
    funext port; cases port <;> rfl
  have highBitInputsEquation : (succBody width).wiring.childInputValues
      hierStep.inputs hierStep.childOutputs .highBit =
        highBitInputs (hierStep.children .highAdder).outputs := by
    funext index; rfl
  have concatInputsEquation : (succBody width).wiring.childInputValues
      hierStep.inputs hierStep.childOutputs .concat =
        concatInputs width (hierStep.children .lowerAdd).outputs
          (hierStep.children .highBit).outputs := by
    funext port; cases port <;> rfl
  rw [lowerLeftInputsEquation] at lowerLeftOutputs
  rw [lowerRightInputsEquation] at lowerRightOutputs
  rw [lowerAddInputsEquation] at lowerResultEquation lowerCarryEquation
  rw [highAdderInputsEquation] at sumEquation carryEquation
  rw [highBitInputsEquation] at highBitOutputs
  rw [concatInputsEquation] at concatEquation
  have lowerLeftValue : (hierStep.children .lowerLeft).outputs .value =
      fun index => hierStep.inputs .left index.castSucc := by
    rw [congrFun lowerLeftOutputs .value]
    funext index
    change (hierStep.children .leftSplit).outputs index.castSucc =
      hierStep.inputs .left index.castSucc
    rw [leftSplitOutputs]
    rfl
  have lowerRightValue : (hierStep.children .lowerRight).outputs .value =
      fun index => hierStep.inputs .right index.castSucc := by
    rw [congrFun lowerRightOutputs .value]
    funext index
    change (hierStep.children .rightSplit).outputs index.castSucc =
      hierStep.inputs .right index.castSucc
    rw [rightSplitOutputs]
    rfl
  have highLeftValue : (hierStep.children .leftSplit).outputs (highIndex width) =
      hierStep.inputs .left (Fin.last width) := by
    rw [leftSplitOutputs]
    rfl
  have highRightValue : (hierStep.children .rightSplit).outputs (highIndex width) =
      hierStep.inputs .right (Fin.last width) := by
    rw [rightSplitOutputs]
    rfl
  have highBitValue : (hierStep.children .highBit).outputs .value =
      fun _ => (hierStep.children .highAdder).outputs .sum := by
    rw [congrFun highBitOutputs .value]
    rfl
  change (hierStep.children .lowerAdd).outputs .result =
    resultValue width ((hierStep.children .lowerLeft).outputs .value)
      ((hierStep.children .lowerRight).outputs .value)
      (hierStep.inputs .carryIn) at lowerResultEquation
  rw [← addBits_result width
    ((hierStep.children .lowerLeft).outputs .value)
    ((hierStep.children .lowerRight).outputs .value)
    (hierStep.inputs .carryIn)] at lowerResultEquation
  rw [lowerLeftValue, lowerRightValue] at lowerResultEquation
  change (hierStep.children .lowerAdd).outputs .carryOut =
    carryValue width ((hierStep.children .lowerLeft).outputs .value)
      ((hierStep.children .lowerRight).outputs .value)
      (hierStep.inputs .carryIn) at lowerCarryEquation
  rw [← addBits_carry width
    ((hierStep.children .lowerLeft).outputs .value)
    ((hierStep.children .lowerRight).outputs .value)
    (hierStep.inputs .carryIn)] at lowerCarryEquation
  rw [lowerLeftValue, lowerRightValue] at lowerCarryEquation
  change (hierStep.children .highAdder).outputs .sum = FullAdder.sumValue
    ((hierStep.children .leftSplit).outputs (highIndex width))
    ((hierStep.children .rightSplit).outputs (highIndex width))
    ((hierStep.children .lowerAdd).outputs .carryOut) at sumEquation
  change (hierStep.children .highAdder).outputs .carryOut = FullAdder.carryValue
    ((hierStep.children .leftSplit).outputs (highIndex width))
    ((hierStep.children .rightSplit).outputs (highIndex width))
    ((hierStep.children .lowerAdd).outputs .carryOut) at carryEquation
  rw [highLeftValue, highRightValue] at sumEquation carryEquation
  rw [lowerCarryEquation] at sumEquation carryEquation
  change (hierStep.children .concat).outputs .result = VectorConcat.concat
    ((hierStep.children .lowerAdd).outputs .result)
    ((hierStep.children .highBit).outputs .value) at concatEquation
  rw [highBitValue] at concatEquation
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [applyRule_holds_iff]
    dsimp only
    constructor
    · rw [← addBits_result (width + 1) (hierStep.inputs .left)
          (hierStep.inputs .right) (hierStep.inputs .carryIn)]
      rw [show hierStep.outputs .result =
          (hierStep.children .concat).outputs .result by exact boundary .result]
      rw [concatEquation]
      change VectorConcat.concat ((hierStep.children .lowerAdd).outputs .result)
          (fun _ => (hierStep.children .highAdder).outputs .sum) = _
      rw [lowerResultEquation, sumEquation]
      exact concat_single_eq_lastCases _ _
    · rw [← addBits_carry (width + 1) (hierStep.inputs .left)
          (hierStep.inputs .right) (hierStep.inputs .carryIn)]
      change hierStep.outputs .carryOut = _
      rw [boundary .carryOut]
      change (hierStep.children .highAdder).outputs .carryOut = _
      rw [carryEquation]
      rfl
  · funext label
    exact nomatch label

private noncomputable opaque succCertifiedLayer (width : Nat) :
    Contracts.Cycle.ModuleCycleCertifiedLayer (succBody width)
      (succChildContracts width) (cycleContract (width + 1)) :=
  RuleSchedules.certifiedLayer (succSchedules width) (succCoversChildren width)
    (fun _ _ _ => True) (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩)
    (succImplements width)

private noncomputable def succCertifiedChildren (width : Nat)
    (previous : Implementation width) :
    ChildStructures (succBody width) (succChildContracts width)
  | .leftSplit => (operandSplitter width).certified.certifiedStructure
  | .rightSplit => (operandSplitter width).certified.certifiedStructure
  | .lowerLeft => (lowerCombiner width).certified.certifiedStructure
  | .lowerRight => (lowerCombiner width).certified.certifiedStructure
  | .lowerAdd => previous.certified.certifiedStructure
  | .highAdder => FullAdder.certified.certifiedStructure
  | .highBit => highCombiner.certified.certifiedStructure
  | .concat => (VectorConcat.certified .bit width 1).certifiedStructure

private noncomputable def succImplementation (width : Nat)
    (previous : Implementation width) : Implementation (width + 1) :=
  ((succCertifiedLayer width).certify
    (succCertifiedChildren width previous)).transportStructure (by
      unfold Contracts.Cycle.Certification.Layer.moduleStructure
        succCertifiedChildren Contracts.Cycle.ModuleCycleCertified.certifiedStructure
      rw [moduleStructure.eq_def]
      congr
      funext child
      cases child <;> rfl)

private noncomputable def implementationDefinition :
    (width : Nat) → Implementation width
  | 0 => baseImplementation
  | width + 1 => succImplementation width (implementationDefinition width)

private noncomputable opaque implementation (width : Nat) :
    Implementation width := implementationDefinition width

noncomputable opaque certification (width : Nat) :
    Contracts.Cycle.ModuleCycleCertification
      (moduleStructure width) (cycleContract width) :=
  implementation width

noncomputable def certified (width : Nat) :
    Contracts.Cycle.ModuleCycleCertified (ports width) :=
  (certification width).bundle

end Silean.Modules.AddWithCarry
