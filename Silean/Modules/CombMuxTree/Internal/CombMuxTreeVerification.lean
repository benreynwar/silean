import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Modules.CombMuxTree.CombMuxTree
import Silean.Modules.Mux.MuxTheorems
import Silean.Modules.VectorSplit.VectorSplitTheorems

/-! # Combinational mux-tree verification

Schedules and recursive certification for the mux tree in `CombMuxTree.lean`.
Import `CombMuxTreeTheorems.lean` for the public proof interface. -/

namespace Silean.Modules.CombMuxTree

open Silean
open Contracts.Cycle.Certification.Layer
open Internal

private abbrev Implementation (element : SignalType) (indexWidth : Nat) :=
  Contracts.Cycle.ModuleCycleCertification (moduleStructure element indexWidth)
    (cycleContract element indexWidth)

private def Implementation.certified
    (implementation : Implementation element indexWidth) :
    Contracts.Cycle.ModuleCycleCertified (ports element indexWidth) := implementation.bundle

@[reducible] private def baseChildContracts (element : SignalType) :
    Contracts.Cycle.ChildCycleContracts (baseBody element)
  | .split => (baseSplitter element).cycleContract

private abbrev baseOccurrence (element : SignalType) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (baseBody element) (baseChildContracts element) :=
  ⟨.split, Composition.SignalComponentRule.apply⟩

private def baseScheduleOrders (element : SignalType) :
    ScheduleDerivation.RuleScheduleOrders (baseBody element)
      (baseChildContracts element) (cycleContract element 0) where
  output | .apply => [baseOccurrence element]
  state := []

private def baseDerivedRuleSchedules (element : SignalType) :
    ScheduleDerivation.DerivedRuleSchedules (baseBody element)
      (baseChildContracts element) (cycleContract element 0) := by
  derive_rule_schedules (baseScheduleOrders element)

private abbrev baseSchedules (element : SignalType) :=
  (baseDerivedRuleSchedules element).schedules

private theorem baseCoversChildren (element : SignalType) :
    (baseSchedules element).CoversChildren :=
  (baseDerivedRuleSchedules element).coversChildren

private def baseSplitInputs (element : SignalType)
    (inputs : (ports element 0).inputs.Values) :
    (baseSplitter element).ports.inputs.Values
  | .value => inputs .values

private theorem baseImplements (element : SignalType)
    (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
      (baseBody element) (baseChildContracts element)) :
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure (baseBody element) layerChildren)
      (cycleContract element 0)
      (fun _ _ => True) := by
  intro contractState hierStep corresponds satisfies
  have boundary := satisfies.1
  derive_empty_state_child_matches childMatch for baseBody element from
    layerChildren, hierStep, satisfies
  have splitOutputs : (hierStep.children .split).outputs =
      (baseSplitter element).outputValues
        (baseSplitInputs element hierStep.inputs) := by
    have holds := (Composition.SignalSplitter.outputRule_holds_iff
      (baseSplitter element) _ _ _).mp
      ((childMatch .split).ruleHolds Composition.SignalComponentRule.apply)
    have inputsEqual : (baseBody element).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .split =
          baseSplitInputs element hierStep.inputs := by
      funext port
      cases port
      rfl
    rw [inputsEqual] at holds
    exact holds
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    change hierStep.outputs .result = _
    rw [show hierStep.outputs .result =
        (hierStep.children .split).outputs ⟨0, by omega⟩ by
      exact boundary .result]
    rw [congrFun splitOutputs ⟨0, by omega⟩]
    rfl
  · rfl

private noncomputable opaque baseCertifiedLayer (element : SignalType) :
    Contracts.Cycle.ModuleCycleCertifiedLayer (baseBody element)
      (baseChildContracts element) (cycleContract element 0) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (baseSchedules element) (baseCoversChildren element) (fun _ _ _ => True)
    (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩) (baseImplements element)

private noncomputable def baseCertifiedChildren (element : SignalType) :
    Contracts.Cycle.Certification.Layer.ChildStructures
      (baseBody element) (baseChildContracts element)
  | .split => (baseSplitter element).certified.certifiedStructure

private noncomputable def baseImplementation (element : SignalType) : Implementation element 0 :=
  ((baseCertifiedLayer element).certify (baseCertifiedChildren element)).transportStructure (by rfl)

@[reducible] private def succChildContracts (element : SignalType) (indexWidth : Nat) :
    Contracts.Cycle.ChildCycleContracts (succBody element indexWidth)
  | .valuesSplit => VectorSplit.cycleContract element
      (BinaryToOneHot.size indexWidth) (BinaryToOneHot.size indexWidth)
  | .indexSplit => (indexSplitter indexWidth).cycleContract
  | .indexLower => (indexLowerCombiner indexWidth).cycleContract
  | .lower | .upper => cycleContract element indexWidth
  | .mux => Mux.cycleContract element

private abbrev valuesSplitOccurrence (element : SignalType)
    (indexWidth : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody element indexWidth) (succChildContracts element indexWidth) :=
  ⟨.valuesSplit, VectorSplit.Rule.apply⟩
private abbrev indexSplitOccurrence (element : SignalType)
    (indexWidth : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody element indexWidth) (succChildContracts element indexWidth) :=
  ⟨.indexSplit, Composition.SignalComponentRule.apply⟩
private abbrev indexLowerOccurrence (element : SignalType)
    (indexWidth : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody element indexWidth) (succChildContracts element indexWidth) :=
  ⟨.indexLower, Composition.SignalComponentRule.apply⟩
private abbrev lowerOccurrence (element : SignalType)
    (indexWidth : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody element indexWidth) (succChildContracts element indexWidth) :=
  ⟨.lower, Rule.apply⟩
private abbrev upperOccurrence (element : SignalType)
    (indexWidth : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody element indexWidth) (succChildContracts element indexWidth) :=
  ⟨.upper, Rule.apply⟩
private abbrev muxOccurrence (element : SignalType)
    (indexWidth : Nat) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody element indexWidth) (succChildContracts element indexWidth) :=
  ⟨.mux, Mux.Rule.select⟩

private def succScheduleOrders (element : SignalType) (indexWidth : Nat) :
    ScheduleDerivation.RuleScheduleOrders (succBody element indexWidth)
      (succChildContracts element indexWidth)
      (cycleContract element (indexWidth + 1)) where
  output := fun
    | .apply => [valuesSplitOccurrence element indexWidth,
        indexSplitOccurrence element indexWidth,
        indexLowerOccurrence element indexWidth,
        lowerOccurrence element indexWidth, upperOccurrence element indexWidth,
        muxOccurrence element indexWidth]
  state := []

private def succDerivedRuleSchedules (element : SignalType) (indexWidth : Nat) :
    ScheduleDerivation.DerivedRuleSchedules (succBody element indexWidth)
      (succChildContracts element indexWidth)
      (cycleContract element (indexWidth + 1)) := by
  derive_rule_schedules (succScheduleOrders element indexWidth)

private abbrev succSchedules (element : SignalType) (indexWidth : Nat) :=
  (succDerivedRuleSchedules element indexWidth).schedules

private theorem succCoversChildren (element : SignalType) (indexWidth : Nat) :
    (succSchedules element indexWidth).CoversChildren :=
  (succDerivedRuleSchedules element indexWidth).coversChildren

private def valuesSplitInputs (element : SignalType) (indexWidth : Nat)
    (inputs : (ports element (indexWidth + 1)).inputs.Values) :
    (VectorSplit.ports element (BinaryToOneHot.size indexWidth)
      (BinaryToOneHot.size indexWidth)).inputs.Values
  | .value => inputs .values

private def indexSplitInputs (element : SignalType) (indexWidth : Nat)
    (inputs : (ports element (indexWidth + 1)).inputs.Values) :
    (indexSplitter indexWidth).ports.inputs.Values
  | .value => inputs .index

private def indexLowerInputs (indexWidth : Nat)
    (split : (indexSplitter indexWidth).ports.outputs.Values) :
    (indexLowerCombiner indexWidth).ports.inputs.Values := fun lowerIndex =>
  split lowerIndex.castSucc

private def lowerInputs (element : SignalType) (indexWidth : Nat)
    (values : (VectorSplit.ports element (BinaryToOneHot.size indexWidth)
      (BinaryToOneHot.size indexWidth)).outputs.Values)
    (lowerBits : (indexLowerCombiner indexWidth).ports.outputs.Values) :
    (ports element indexWidth).inputs.Values
  | .values => values .left
  | .index => lowerBits .value

private def upperInputs (element : SignalType) (indexWidth : Nat)
    (values : (VectorSplit.ports element (BinaryToOneHot.size indexWidth)
      (BinaryToOneHot.size indexWidth)).outputs.Values)
    (lowerBits : (indexLowerCombiner indexWidth).ports.outputs.Values) :
    (ports element indexWidth).inputs.Values
  | .values => values .right
  | .index => lowerBits .value

private def muxInputs (element : SignalType) (indexWidth : Nat)
    (index : (indexSplitter indexWidth).ports.outputs.Values)
    (lower upper : (ports element indexWidth).outputs.Values) :
    (Mux.ports element).inputs.Values
  | .select => index (highIndex indexWidth)
  | .whenFalse => lower .result
  | .whenTrue => upper .result

private theorem succImplements (element : SignalType) (indexWidth : Nat)
    (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
      (succBody element indexWidth) (succChildContracts element indexWidth)) :
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (succBody element indexWidth) layerChildren)
      (cycleContract element (indexWidth + 1)) (fun _ _ => True) := by
  intro contractState hierStep corresponds satisfies
  have boundary := satisfies.1
  derive_empty_state_child_matches childMatch for succBody element indexWidth from
    layerChildren, hierStep, satisfies
  have indexOutputs : (hierStep.children .indexSplit).outputs =
      (indexSplitter indexWidth).outputValues
        (indexSplitInputs element indexWidth hierStep.inputs) := by
    have holds := (Composition.SignalSplitter.outputRule_holds_iff
      (indexSplitter indexWidth) _ _ _).mp
      ((childMatch .indexSplit).ruleHolds Composition.SignalComponentRule.apply)
    have inputsEqual : (succBody element indexWidth).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .indexSplit =
          indexSplitInputs element indexWidth hierStep.inputs := by
      funext port
      cases port
      rfl
    rw [inputsEqual] at holds
    exact holds
  have lowerOutputs : (hierStep.children .indexLower).outputs =
      (indexLowerCombiner indexWidth).outputValues
        ((succBody element indexWidth).wiring.childInputValues
          hierStep.inputs hierStep.childOutputs .indexLower) := by
    exact (Composition.SignalCombiner.outputRule_holds_iff
      (indexLowerCombiner indexWidth) _ _ _).mp
      ((childMatch .indexLower).ruleHolds Composition.SignalComponentRule.apply)

  let rootValues : Fin (BinaryToOneHot.size (indexWidth + 1)) → element.Denote :=
    fun index => hierStep.inputs .values index
  let rootIndex : Fin (indexWidth + 1) → Bool :=
    fun index => hierStep.inputs .index index
  let leftValues : Fin (BinaryToOneHot.size indexWidth) → element.Denote :=
    (hierStep.children .valuesSplit).outputs .left
  let rightValues : Fin (BinaryToOneHot.size indexWidth) → element.Denote :=
    (hierStep.children .valuesSplit).outputs .right
  let lowerIndexBits : Fin indexWidth → Bool :=
    (hierStep.children .indexLower).outputs .value
  let highBit : Bool :=
    (hierStep.children .indexSplit).outputs (highIndex indexWidth)
  let lowerResult : element.Denote :=
    (hierStep.children .lower).outputs .result
  let upperResult : element.Denote :=
    (hierStep.children .upper).outputs .result
  let muxResult : element.Denote :=
    (hierStep.children .mux).outputs .result

  have valuesEquation := VectorSplit.outputs_of_allowed element
    (BinaryToOneHot.size indexWidth) (BinaryToOneHot.size indexWidth)
    (childMatch .valuesSplit).allowed
  change leftValues = VectorSplit.leftPart rootValues ∧
    rightValues = VectorSplit.rightPart rootValues at valuesEquation

  have lowerEquation := (outputRule_holds_iff element indexWidth
    _ SignalMap.emptyValues _).mp ((childMatch .lower).ruleHolds Rule.apply)
  change lowerResult = select indexWidth leftValues lowerIndexBits at lowerEquation

  have upperEquation := (outputRule_holds_iff element indexWidth
    _ SignalMap.emptyValues _).mp ((childMatch .upper).ruleHolds Rule.apply)
  change upperResult = select indexWidth rightValues lowerIndexBits at upperEquation

  have muxEquation := Mux.result_of_allowed element (childMatch .mux).allowed
  change muxResult = bif highBit then upperResult else lowerResult at muxEquation

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    change hierStep.outputs .result =
      select (indexWidth + 1) rootValues rootIndex
    rw [show hierStep.outputs .result =
        muxResult by
      exact boundary .result]
    have indexLowerInputsEquation :
        (succBody element indexWidth).wiring.childInputValues
          hierStep.inputs hierStep.childOutputs .indexLower =
          indexLowerInputs indexWidth (hierStep.children .indexSplit).outputs := by
      funext lowerIndex; rfl
    rw [indexLowerInputsEquation] at lowerOutputs
    rw [muxEquation]
    have lowerValue : lowerIndexBits =
        fun lowerIndex => rootIndex lowerIndex.castSucc := by
      dsimp [lowerIndexBits, rootIndex]
      rw [congrFun lowerOutputs .value]
      funext lowerIndex
      change (hierStep.children .indexSplit).outputs lowerIndex.castSucc =
        hierStep.inputs .index lowerIndex.castSucc
      rw [indexOutputs]
      rfl
    have highValue : highBit = rootIndex (Fin.last indexWidth) := by
      dsimp [highBit, rootIndex]
      rw [indexOutputs]
      rfl
    rw [lowerEquation, upperEquation]
    rw [lowerValue, highValue]
    cases high : rootIndex (Fin.last indexWidth)
    · simp only [cond_false]
      rw [valuesEquation.1]
      simp [select, BitVector.toIndex,
        VectorSplit.leftPart, high]
    · simp only [cond_true]
      rw [valuesEquation.2]
      simp [select, BitVector.toIndex,
        VectorSplit.rightPart, high, Fin.natAdd]
  · change SignalMap.emptyValues = SignalMap.emptyValues
    rfl

private noncomputable opaque succCertifiedLayer
    (element : SignalType) (indexWidth : Nat) :
    Contracts.Cycle.ModuleCycleCertifiedLayer (succBody element indexWidth)
      (succChildContracts element indexWidth) (cycleContract element (indexWidth + 1)) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (succSchedules element indexWidth) (succCoversChildren element indexWidth)
    (fun _ _ _ => True) (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩)
    (succImplements element indexWidth)

private noncomputable def succCertifiedChildren (element : SignalType)
    (indexWidth : Nat) (previous : Implementation element indexWidth) :
    Contracts.Cycle.Certification.Layer.ChildStructures
      (succBody element indexWidth) (succChildContracts element indexWidth)
  | .valuesSplit =>
      (VectorSplit.certified element (BinaryToOneHot.size indexWidth)
        (BinaryToOneHot.size indexWidth)).certifiedStructure
  | .indexSplit => (indexSplitter indexWidth).certified.certifiedStructure
  | .indexLower => (indexLowerCombiner indexWidth).certified.certifiedStructure
  | .lower | .upper => previous.certified.certifiedStructure
  | .mux => (Mux.certified element).certifiedStructure

private noncomputable def succImplementation (element : SignalType) (indexWidth : Nat)
    (previous : Implementation element indexWidth) :
    Implementation element (indexWidth + 1) :=
  ((succCertifiedLayer element indexWidth).certify
    (succCertifiedChildren element indexWidth previous)).transportStructure (by
      unfold Contracts.Cycle.Certification.Layer.moduleStructure
        succCertifiedChildren Contracts.Cycle.ModuleCycleCertified.certifiedStructure
      rw [moduleStructure.eq_def]
      congr
      funext child
      cases child <;> rfl)

private noncomputable def implementation (element : SignalType) :
    (indexWidth : Nat) → Implementation element indexWidth
  | 0 => baseImplementation element
  | indexWidth + 1 =>
      succImplementation element indexWidth (implementation element indexWidth)

noncomputable def certification (element : SignalType) (indexWidth : Nat) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure element indexWidth)
      (cycleContract element indexWidth) := implementation element indexWidth

noncomputable def certified (element : SignalType) (indexWidth : Nat) :
    Contracts.Cycle.ModuleCycleCertified (ports element indexWidth) :=
  (certification element indexWidth).bundle


end Silean.Modules.CombMuxTree
