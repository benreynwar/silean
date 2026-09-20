import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Modules.Constant.Constant
import Silean.Modules.HalfAdder.HalfAdderDerived
import Silean.Modules.Increment.Internal.IncrementStructure
import Silean.Modules.VectorConcat.VectorConcatDerived

/-! Internal schedules and inductive certification for `Increment`. -/

namespace Silean.Modules.Increment

open Silean
open Contracts.Cycle.Certification.Layer

namespace Ripple

private abbrev Implementation (width : Nat) :=
  Contracts.Cycle.ModuleCycleCertification (moduleStructure width) (cycleContract width)

private def Implementation.certified (implementation : Implementation width) :
    Contracts.Cycle.ModuleCycleCertified (ports width) := implementation.bundle

@[reducible] private def baseChildContracts : Contracts.Cycle.ChildCycleContracts baseBody
  | .empty => Modules.Constant.cycleContract (.vector 0 .bit) emptyValue

private abbrev baseOccurrence : RuleOccurrence baseBody baseChildContracts :=
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
    rw [outputRule_holds_iff]
    dsimp only
    constructor
    · funext index
      exact Fin.elim0 index
    · rw [show hierStep.outputs .carryOut = hierStep.inputs .carryIn by
          exact boundary .carryOut]
      rfl
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
  | .split => (splitter width).cycleContract
  | .lowerBits => (lowerCombiner width).cycleContract
  | .lowerRipple => cycleContract width
  | .highAdder => HalfAdder.cycleContract
  | .highBit => highCombiner.cycleContract
  | .concat => VectorConcat.cycleContract .bit width 1

private abbrev splitOccurrence (width) :
    RuleOccurrence (succBody width) (succChildContracts width) :=
  ⟨.split, Composition.SignalComponentRule.apply⟩
private abbrev lowerBitsOccurrence (width) :
    RuleOccurrence (succBody width) (succChildContracts width) :=
  ⟨.lowerBits, Composition.SignalComponentRule.apply⟩
private abbrev lowerRippleOccurrence (width) :
    RuleOccurrence (succBody width) (succChildContracts width) :=
  ⟨.lowerRipple, Rule.apply⟩
private abbrev highSumOccurrence (width) :
    RuleOccurrence (succBody width) (succChildContracts width) :=
  ⟨.highAdder, HalfAdder.Rule.sum⟩
private abbrev highCarryOccurrence (width) :
    RuleOccurrence (succBody width) (succChildContracts width) :=
  ⟨.highAdder, HalfAdder.Rule.carry⟩
private abbrev highBitOccurrence (width) :
    RuleOccurrence (succBody width) (succChildContracts width) :=
  ⟨.highBit, Composition.SignalComponentRule.apply⟩
private abbrev concatOccurrence (width) :
    RuleOccurrence (succBody width) (succChildContracts width) :=
  ⟨.concat, VectorConcat.Rule.apply⟩

private def succScheduleOrders (width : Nat) :
    ScheduleDerivation.RuleScheduleOrders (succBody width)
      (succChildContracts width) (cycleContract (width + 1)) where
  output | .apply => [splitOccurrence width, lowerBitsOccurrence width,
    lowerRippleOccurrence width, highSumOccurrence width,
    highCarryOccurrence width, highBitOccurrence width, concatOccurrence width]
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

private def splitInputs (width : Nat)
    (inputs : (ports (width + 1)).inputs.Values) :
    (splitter width).ports.inputs.Values
  | .value => inputs .value

private def lowerBitsInputs (width : Nat)
    (split : (splitter width).ports.outputs.Values) :
    (lowerCombiner width).ports.inputs.Values := fun index => split index.castSucc

private def lowerRippleInputs (width : Nat)
    (inputs : (ports (width + 1)).inputs.Values)
    (lowerBits : (lowerCombiner width).ports.outputs.Values) :
    (ports width).inputs.Values
  | .value => lowerBits .value
  | .carryIn => inputs .carryIn

private def highAdderInputs (width : Nat)
    (split : (splitter width).ports.outputs.Values)
    (lower : (ports width).outputs.Values) : HalfAdder.ports.inputs.Values
  | .left => split (highIndex width)
  | .right => lower .carryOut

private def highBitInputs (adder : HalfAdder.ports.outputs.Values) :
    highCombiner.ports.inputs.Values := fun _ => adder .sum

private def concatInputs (width : Nat) (lower : (ports width).outputs.Values)
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
  have splitOutputs : (hierStep.children .split).outputs =
      (splitter width).outputValues (splitInputs width hierStep.inputs) := by
    have holds := (Composition.SignalSplitter.outputRule_holds_iff
      (splitter width) _ _ _).mp
      ((childMatches .split).ruleHolds Composition.SignalComponentRule.apply)
    have inputsEqual : (succBody width).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .split =
          splitInputs width hierStep.inputs := by
      funext port
      cases port
      rfl
    rw [inputsEqual] at holds
    exact holds
  have lowerBitsOutputs : (hierStep.children .lowerBits).outputs =
      (lowerCombiner width).outputValues ((succBody width).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .lowerBits) :=
    (Composition.SignalCombiner.outputRule_holds_iff
      (lowerCombiner width) _ _ _).mp
      ((childMatches .lowerBits).ruleHolds Composition.SignalComponentRule.apply)
  have highBitOutputs : (hierStep.children .highBit).outputs =
      highCombiner.outputValues ((succBody width).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .highBit) :=
    (Composition.SignalCombiner.outputRule_holds_iff highCombiner _ _ _).mp
      ((childMatches .highBit).ruleHolds Composition.SignalComponentRule.apply)
  have lowerEquation := (outputRule_holds_iff width _
    (childStates .lowerRipple) _).mp
      ((childMatches .lowerRipple).ruleHolds Rule.apply)
  have sumEquation :=
    (childMatches .highAdder).boundaryOutput HalfAdder.cycleContract.sumEquation
  have carryEquation :=
    (childMatches .highAdder).boundaryOutput HalfAdder.cycleContract.carryEquation
  have concatEquation := VectorConcat.cycleContract.result .bit width 1
    (childMatches .concat).allowed
  change (hierStep.children .concat).outputs .result =
    VectorConcat.concat
      ((succBody width).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .concat .left)
      ((succBody width).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .concat .right) at concatEquation
  have lowerBitsInputsEquation : (succBody width).wiring.childInputValues
      hierStep.inputs hierStep.childOutputs .lowerBits =
        lowerBitsInputs width (hierStep.children .split).outputs := by
    funext index; rfl
  have lowerRippleInputsEquation : (succBody width).wiring.childInputValues
      hierStep.inputs hierStep.childOutputs .lowerRipple =
        lowerRippleInputs width hierStep.inputs
          (hierStep.children .lowerBits).outputs := by
    funext port; cases port <;> rfl
  have highAdderInputsEquation : (succBody width).wiring.childInputValues
      hierStep.inputs hierStep.childOutputs .highAdder =
        highAdderInputs width (hierStep.children .split).outputs
          (hierStep.children .lowerRipple).outputs := by
    funext port; cases port <;> rfl
  have highBitInputsEquation : (succBody width).wiring.childInputValues
      hierStep.inputs hierStep.childOutputs .highBit =
        highBitInputs (hierStep.children .highAdder).outputs := by
    funext index; rfl
  have concatInputsEquation : (succBody width).wiring.childInputValues
      hierStep.inputs hierStep.childOutputs .concat =
        concatInputs width (hierStep.children .lowerRipple).outputs
          (hierStep.children .highBit).outputs := by
    funext port; cases port <;> rfl
  rw [lowerBitsInputsEquation] at lowerBitsOutputs
  rw [lowerRippleInputsEquation] at lowerEquation
  rw [highAdderInputsEquation] at sumEquation carryEquation
  rw [highBitInputsEquation] at highBitOutputs
  rw [concatInputsEquation] at concatEquation
  have lowerValue : (hierStep.children .lowerBits).outputs .value =
      fun index => hierStep.inputs .value index.castSucc := by
    rw [congrFun lowerBitsOutputs .value]
    funext index
    change (hierStep.children .split).outputs index.castSucc =
      hierStep.inputs .value index.castSucc
    rw [splitOutputs]
    rfl
  have highValue : (hierStep.children .split).outputs (highIndex width) =
      hierStep.inputs .value (Fin.last width) := by
    rw [splitOutputs]
    rfl
  have highBitValue : (hierStep.children .highBit).outputs .value =
      fun _ => (hierStep.children .highAdder).outputs .sum := by
    rw [congrFun highBitOutputs .value]
    rfl
  have lowerResultEquation := lowerEquation.1
  change (hierStep.children .lowerRipple).outputs .result =
    (addCarry width ((hierStep.children .lowerBits).outputs .value)
      (hierStep.inputs .carryIn)).1 at lowerResultEquation
  rw [lowerValue] at lowerResultEquation
  have lowerCarryEquation := lowerEquation.2
  change (hierStep.children .lowerRipple).outputs .carryOut =
    (addCarry width ((hierStep.children .lowerBits).outputs .value)
      (hierStep.inputs .carryIn)).2 at lowerCarryEquation
  rw [lowerValue] at lowerCarryEquation
  change (hierStep.children .highAdder).outputs .sum = HalfAdder.sumValue
    ((hierStep.children .split).outputs (highIndex width))
    ((hierStep.children .lowerRipple).outputs .carryOut) at sumEquation
  change (hierStep.children .highAdder).outputs .carry = HalfAdder.carryValue
    ((hierStep.children .split).outputs (highIndex width))
    ((hierStep.children .lowerRipple).outputs .carryOut) at carryEquation
  rw [highValue] at sumEquation carryEquation
  rw [lowerCarryEquation] at sumEquation carryEquation
  change (hierStep.children .concat).outputs .result = VectorConcat.concat
    ((hierStep.children .lowerRipple).outputs .result)
    ((hierStep.children .highBit).outputs .value) at concatEquation
  rw [highBitValue] at concatEquation
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    dsimp only
    constructor
    · rw [show hierStep.outputs .result =
          (hierStep.children .concat).outputs .result by exact boundary .result]
      rw [concatEquation]
      change VectorConcat.concat ((hierStep.children .lowerRipple).outputs .result)
          (fun _ => (hierStep.children .highAdder).outputs .sum) = _
      rw [lowerResultEquation, sumEquation]
      exact concat_single_eq_lastCases _ _
    · change hierStep.outputs .carryOut = _
      rw [boundary .carryOut]
      change (hierStep.children .highAdder).outputs .carry = _
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
  | .split => (splitter width).certified.certifiedStructure
  | .lowerBits => (lowerCombiner width).certified.certifiedStructure
  | .lowerRipple => previous.certified.certifiedStructure
  | .highAdder => HalfAdder.certified.certifiedStructure
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

noncomputable def certification (width : Nat) :
    Contracts.Cycle.ModuleCycleCertification
      (moduleStructure width) (cycleContract width) :=
  implementation width

noncomputable def certified (width : Nat) :
    Contracts.Cycle.ModuleCycleCertified (ports width) :=
  (certification width).bundle

end Ripple

@[reducible] private def childContracts (width : Nat) :
    Contracts.Cycle.ChildCycleContracts (body width)
  | .one => Modules.Constant.cycleContract .bit true
  | .ripple => Ripple.cycleContract width

private abbrev oneOccurrence (width : Nat) :
    RuleOccurrence (body width) (childContracts width) :=
  ⟨.one, Primitives.ConstantRule.apply⟩

private abbrev rippleOccurrence (width : Nat) :
    RuleOccurrence (body width) (childContracts width) :=
  ⟨.ripple, Ripple.Rule.apply⟩

private def scheduleOrders (width : Nat) : ScheduleDerivation.RuleScheduleOrders
    (body width) (childContracts width) (cycleContract width) where
  output | .apply => [oneOccurrence width, rippleOccurrence width]
  state := []

private def derivedRuleSchedules (width : Nat) :
    ScheduleDerivation.DerivedRuleSchedules
      (body width) (childContracts width) (cycleContract width) := by
  derive_rule_schedules (scheduleOrders width)

private abbrev schedules (width : Nat) :=
  (derivedRuleSchedules width).schedules

private theorem coversChildren (width : Nat) :
    (schedules width).CoversChildren :=
  (derivedRuleSchedules width).coversChildren

private theorem compositeImplements (width : Nat)
    (layerChildren : ChildStructures (body width) (childContracts width)) :
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure (body width) layerChildren)
      (cycleContract width) (fun _ _ => True) := by
  intro contractState hierStep corresponds satisfies
  have boundary := satisfies.1
  have childStates : ∀ child, (childContracts width child).state.Values := by
    intro child
    cases child <;> exact SignalMap.emptyValues
  have childStateSubsingleton : ∀ child,
      Subsingleton (childContracts width child).state.Values := by
    intro child
    cases child <;> change Subsingleton emptySignalMap.Values <;> infer_instance
  have childMatches := childSolutionsMatchContracts_of_subsingletonState
    (body := body width) layerChildren hierStep satisfies childStates
      childStateSubsingleton
  let inputValue : Fin width → Bool := fun index => hierStep.inputs .value index
  let oneValue : Bool := (hierStep.children .one).outputs .output
  let rippleResult : Fin width → Bool :=
    (hierStep.children .ripple).outputs .result
  let rippleCarry : Bool := (hierStep.children .ripple).outputs .carryOut
  have oneEquation := Modules.Constant.output_of_allowed .bit true
    (childMatches .one).allowed
  change oneValue = true at oneEquation
  have rippleEquation := (Ripple.outputRule_holds_iff width _
    (childStates .ripple) _).mp ((childMatches .ripple).ruleHolds Ripple.Rule.apply)
  change rippleResult = (addCarry width inputValue oneValue).1 ∧
    rippleCarry = (addCarry width inputValue oneValue).2 at rippleEquation
  have resultEquation := rippleEquation.1
  rw [oneEquation] at resultEquation
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [applyRule_holds_iff]
    change hierStep.outputs .result = incrementValue width inputValue
    rw [show hierStep.outputs .result = rippleResult by exact boundary .result]
    change rippleResult = (addCarry width inputValue true).1
    exact resultEquation
  · funext label
    exact nomatch label

private noncomputable opaque certifiedLayer (width : Nat) :
    Contracts.Cycle.ModuleCycleCertifiedLayer (body width)
      (childContracts width) (cycleContract width) :=
  RuleSchedules.certifiedLayer (schedules width) (coversChildren width)
    (fun _ _ _ => True) (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩)
    (compositeImplements width)

@[reducible] private noncomputable def certifiedChildren (width : Nat) :
    ChildStructures (body width) (childContracts width)
  | .one => (Modules.Constant.certified .bit true).certifiedStructure
  | .ripple => (Ripple.certified width).certifiedStructure

noncomputable def certification (width : Nat) :
    Contracts.Cycle.ModuleCycleCertification
      (moduleStructure width) (cycleContract width) :=
  ((certifiedLayer width).certify (certifiedChildren width)).transportStructure (by
    unfold Contracts.Cycle.Certification.Layer.moduleStructure
      certifiedChildren Contracts.Cycle.ModuleCycleCertified.certifiedStructure
    unfold moduleStructure
    congr
    funext child
    cases child <;> rfl)

noncomputable def certified (width : Nat) :
    Contracts.Cycle.ModuleCycleCertified (ports width) :=
  (certification width).bundle

end Silean.Modules.Increment
