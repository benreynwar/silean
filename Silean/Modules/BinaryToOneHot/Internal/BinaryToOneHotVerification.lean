import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Modules.BinaryToOneHot.BinaryToOneHot
import Silean.Modules.VectorConcat.VectorConcatTheorems

/-! # Binary-to-one-hot verification

Schedules and recursive certification for the hardware family in
`BinaryToOneHot.lean`. Import `BinaryToOneHotTheorems.lean` for the public
proof interface. -/

namespace Silean.Modules.BinaryToOneHot

open Silean
open Contracts.Cycle.Certification.Layer
open Internal

private abbrev Implementation (width : Nat) :=
  Contracts.Cycle.ModuleCycleCertification (moduleStructure width) (cycleContract width)

private def Implementation.certified (implementation : Implementation width) :
    Contracts.Cycle.ModuleCycleCertified (ports width) := implementation.bundle

@[reducible] private def baseChildContracts : Contracts.Cycle.ChildCycleContracts baseBody
  | .constant => Modules.Constant.cycleContract (.vector 1 .bit) baseValue

private abbrev baseOccurrence :
    Contracts.Cycle.Certification.Layer.RuleOccurrence baseBody baseChildContracts :=
  ⟨.constant, Primitives.ConstantRule.apply⟩

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
    (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
      baseBody baseChildContracts) :
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure baseBody layerChildren)
      (cycleContract 0) (fun _ _ => True) := by
  intro contractState hierStep corresponds satisfies
  have boundary := satisfies.1
  derive_empty_state_child_matches childMatch for baseBody from
    layerChildren, hierStep, satisfies
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    funext index
    change hierStep.outputs .result index = _
    have boundaryResult := boundary .result
    rw [congrFun boundaryResult index]
    have constantRule := (Modules.Constant.outputRule_holds_iff
      (.vector 1 .bit) baseValue _ SignalMap.emptyValues _).mp
      ((childMatch .constant).ruleHolds Primitives.ConstantRule.apply)
    change (hierStep.children .constant).outputs .output index = _
    exact (congrFun constantRule index).trans (by
      simp [baseValue, oneHot, BitVector.toNat])
  · change SignalMap.emptyValues = SignalMap.emptyValues
    rfl

private noncomputable opaque baseCertifiedLayer :
    Contracts.Cycle.ModuleCycleCertifiedLayer baseBody baseChildContracts
      (cycleContract 0) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    baseSchedules baseCoversChildren (fun _ _ _ => True)
    (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩) baseImplements

private noncomputable def baseCertifiedChildren :
    Contracts.Cycle.Certification.Layer.ChildStructures baseBody baseChildContracts
  | .constant =>
      (Modules.Constant.certified (.vector 1 .bit) baseValue).certifiedStructure

private noncomputable def baseImplementation : Implementation 0 :=
  (baseCertifiedLayer.certify baseCertifiedChildren).transportStructure (by rfl)

@[reducible] private def succChildContracts (width : Nat) :
    Contracts.Cycle.ChildCycleContracts (succBody width)
  | .split => (splitter width).cycleContract
  | .lowerBits => (lowerCombiner width).cycleContract
  | .decode => cycleContract width
  | .invert => Primitives.notCycleContract
  | .lowerMask | .upperMask => Modules.Mask.cycleContract (.vector (size width) .bit)
  | .concat => Modules.VectorConcat.cycleContract .bit (size width) (size width)

private abbrev splitOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody width) (succChildContracts width) :=
  ⟨.split, Composition.SignalComponentRule.apply⟩
private abbrev lowerBitsOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody width) (succChildContracts width) :=
  ⟨.lowerBits, Composition.SignalComponentRule.apply⟩
private abbrev decodeOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody width) (succChildContracts width) :=
  ⟨.decode, Rule.apply⟩
private abbrev invertOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody width) (succChildContracts width) :=
  ⟨.invert, Primitives.NotRule.apply⟩
private abbrev lowerOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody width) (succChildContracts width) :=
  ⟨.lowerMask, Modules.Mask.Rule.apply⟩
private abbrev upperOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody width) (succChildContracts width) :=
  ⟨.upperMask, Modules.Mask.Rule.apply⟩
private abbrev concatOccurrence (width) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (succBody width) (succChildContracts width) :=
  ⟨.concat, Modules.VectorConcat.Rule.apply⟩

private def succScheduleOrders (width : Nat) :
    ScheduleDerivation.RuleScheduleOrders (succBody width)
      (succChildContracts width) (cycleContract (width + 1)) where
  output := fun
    | .apply => [splitOccurrence width, lowerBitsOccurrence width,
        decodeOccurrence width, invertOccurrence width, lowerOccurrence width,
        upperOccurrence width, concatOccurrence width]
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

private def splitInputs (width : Nat) (inputs : (ports (width + 1)).inputs.Values) :
    (splitter width).ports.inputs.Values
  | .value => inputs .value

private def lowerBitsInputs (width : Nat)
    (split : (splitter width).ports.outputs.Values) :
    (lowerCombiner width).ports.inputs.Values := fun index =>
  split index.castSucc

private def decodeInputs (width : Nat)
    (lowerBits : (lowerCombiner width).ports.outputs.Values) :
    (ports width).inputs.Values
  | .value => lowerBits .value

private def invertInputs (width : Nat)
    (split : (splitter width).ports.outputs.Values) :
    Primitives.not.ports.inputs.Values
  | .input => split (highIndex width)

private def lowerInputs (width : Nat)
    (decoded : (ports width).outputs.Values)
    (inverted : Primitives.not.ports.outputs.Values) :
    (Modules.Mask.ports (.vector (size width) .bit)).inputs.Values
  | .value => decoded .result
  | .mask => inverted .output

private def upperInputs (width : Nat)
    (split : (splitter width).ports.outputs.Values)
    (decoded : (ports width).outputs.Values) :
    (Modules.Mask.ports (.vector (size width) .bit)).inputs.Values
  | .value => decoded .result
  | .mask => split (highIndex width)

private def concatInputs (width : Nat)
    (lower upper : (Modules.Mask.ports (.vector (size width) .bit)).outputs.Values) :
    (Modules.VectorConcat.ports .bit (size width) (size width)).inputs.Values
  | .left => lower .result
  | .right => upper .result

private theorem succImplements (width : Nat)
    (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
      (succBody width) (succChildContracts width)) :
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure (succBody width) layerChildren)
      (cycleContract (width + 1))
      (fun _ _ => True) := by
  intro contractState hierStep corresponds satisfies
  have boundary := satisfies.1
  derive_empty_state_child_matches childMatch for succBody width from
    layerChildren, hierStep, satisfies
  have splitOutputs : (hierStep.children .split).outputs =
      (splitter width).outputValues (splitInputs width hierStep.inputs) := by
    have holds := (Composition.SignalSplitter.outputRule_holds_iff
      (splitter width) _ _ _).mp
      ((childMatch .split).ruleHolds Composition.SignalComponentRule.apply)
    have inputsEqual : (succBody width).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .split =
          splitInputs width hierStep.inputs := by
      funext port
      cases port
      rfl
    rw [inputsEqual] at holds
    exact holds
  have lowerOutputs : (hierStep.children .lowerBits).outputs =
      (lowerCombiner width).outputValues
        ((succBody width).wiring.childInputValues
          hierStep.inputs hierStep.childOutputs .lowerBits) := by
    exact (Composition.SignalCombiner.outputRule_holds_iff
      (lowerCombiner width) _ _ _).mp
      ((childMatch .lowerBits).ruleHolds Composition.SignalComponentRule.apply)

  have decodedEquation := (outputRule_holds_iff width _ SignalMap.emptyValues _).mp
    ((childMatch .decode).ruleHolds Rule.apply)

  have invertEquation := (Primitives.notOutputRule_holds_iff
    _ SignalMap.emptyValues _).mp
    ((childMatch .invert).ruleHolds Primitives.NotRule.apply)

  have lowerEquation := (Modules.Mask.outputRule_holds_iff
    (.vector (size width) .bit) _ SignalMap.emptyValues _).mp
      ((childMatch .lowerMask).ruleHolds Modules.Mask.Rule.apply)

  have upperEquation := (Modules.Mask.outputRule_holds_iff
    (.vector (size width) .bit) _ SignalMap.emptyValues _).mp
      ((childMatch .upperMask).ruleHolds Modules.Mask.Rule.apply)

  have concatEquation := (Modules.VectorConcat.outputRule_holds_iff
    .bit (size width) (size width) _ SignalMap.emptyValues _).mp
      ((childMatch .concat).ruleHolds Modules.VectorConcat.Rule.apply)

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    rw [oneHot_eq_decode]
    change hierStep.outputs .result = decode (width + 1) (hierStep.inputs .value)
    rw [show hierStep.outputs .result =
        (hierStep.children .concat).outputs .result by exact boundary .result]
    have lowerBitsInputsEquation : (succBody width).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .lowerBits =
          lowerBitsInputs width (hierStep.children .split).outputs := by
      funext index
      rfl
    have decodeInputsEquation : (succBody width).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .decode =
          decodeInputs width (hierStep.children .lowerBits).outputs := by
      funext port; cases port; rfl
    have invertInputsEquation : (succBody width).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .invert =
          invertInputs width (hierStep.children .split).outputs := by
      funext port; cases port; rfl
    have lowerInputsEquation : (succBody width).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .lowerMask =
          lowerInputs width (hierStep.children .decode).outputs
            (hierStep.children .invert).outputs := by
      funext port; cases port <;> rfl
    have upperInputsEquation : (succBody width).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .upperMask =
          upperInputs width (hierStep.children .split).outputs
            (hierStep.children .decode).outputs := by
      funext port; cases port <;> rfl
    have concatInputsEquation : (succBody width).wiring.childInputValues
        hierStep.inputs hierStep.childOutputs .concat =
          concatInputs width (hierStep.children .lowerMask).outputs
            (hierStep.children .upperMask).outputs := by
      funext port; cases port <;> rfl
    rw [lowerInputsEquation] at lowerEquation
    rw [upperInputsEquation] at upperEquation
    rw [decodeInputsEquation] at decodedEquation
    rw [oneHot_eq_decode] at decodedEquation
    rw [invertInputsEquation] at invertEquation
    rw [lowerBitsInputsEquation] at lowerOutputs
    rw [concatInputsEquation] at concatEquation
    have lowerValue : (hierStep.children .lowerBits).outputs .value =
        fun index => hierStep.inputs .value index.castSucc := by
      rw [congrFun lowerOutputs .value]
      funext index
      change (hierStep.children .split).outputs index.castSucc =
        hierStep.inputs .value index.castSucc
      rw [splitOutputs]
      rfl
    have splitHigh : (hierStep.children .split).outputs (highIndex width) =
        hierStep.inputs .value (Fin.last width) := by
      rw [splitOutputs]
      rfl
    change (hierStep.children .decode).outputs .result =
      decode width ((hierStep.children .lowerBits).outputs .value) at decodedEquation
    rw [lowerValue] at decodedEquation
    change (hierStep.children .invert).outputs .output =
      !(hierStep.children .split).outputs (highIndex width) at invertEquation
    rw [splitHigh] at invertEquation
    change hierStep.childOutputs .concat .result = _
    rw [concatEquation]
    funext index
    refine Fin.addCases ?_ ?_ index
    · intro lowerIndex
      rw [Modules.VectorConcat.concat_left]
      change hierStep.childOutputs .lowerMask .result lowerIndex = _
      rw [congrFun lowerEquation lowerIndex]
      simp [lowerInputs, SignalType.mask]
      rw [congrFun decodedEquation lowerIndex, invertEquation]
      simp only [decode, Fin.addCases_left]
      exact Bool.and_comm _ _
    · intro upperIndex
      rw [Modules.VectorConcat.concat_right]
      change hierStep.childOutputs .upperMask .result upperIndex = _
      rw [congrFun upperEquation upperIndex]
      simp [upperInputs, SignalType.mask]
      rw [congrFun decodedEquation upperIndex]
      rw [splitHigh]
      simp only [decode]
      rw [Bool.and_comm (decode width
        (fun index => hierStep.inputs .value index.castSucc) upperIndex)
          (hierStep.inputs .value (Fin.last width))]
      symm
      rw [show upperIndex.addNat (size width) =
          Fin.natAdd (size width) upperIndex by
        apply Fin.ext
        simp [Fin.addNat, Fin.natAdd, Nat.add_comm]]
      apply Fin.addCases_right
  · change SignalMap.emptyValues = SignalMap.emptyValues
    rfl

private noncomputable opaque succCertifiedLayer (width : Nat) :
    Contracts.Cycle.ModuleCycleCertifiedLayer (succBody width)
      (succChildContracts width) (cycleContract (width + 1)) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (succSchedules width) (succCoversChildren width) (fun _ _ _ => True)
    (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩) (succImplements width)

private noncomputable def succCertifiedChildren (width : Nat)
    (previous : Implementation width) :
    Contracts.Cycle.Certification.Layer.ChildStructures
      (succBody width) (succChildContracts width)
  | .split => (splitter width).certified.certifiedStructure
  | .lowerBits => (lowerCombiner width).certified.certifiedStructure
  | .decode => previous.certified.certifiedStructure
  | .invert => Primitives.notCertified.certifiedStructure
  | .lowerMask | .upperMask =>
      (Modules.Mask.certified (.vector (size width) .bit)).certifiedStructure
  | .concat =>
      (Modules.VectorConcat.certified .bit (size width) (size width)).certifiedStructure

private noncomputable def succImplementation (width : Nat)
    (previous : Implementation width) : Implementation (width + 1) :=
  ((succCertifiedLayer width).certify (succCertifiedChildren width previous)).transportStructure
    (by
      unfold Contracts.Cycle.Certification.Layer.moduleStructure
        succCertifiedChildren Contracts.Cycle.ModuleCycleCertified.certifiedStructure
      rw [moduleStructure.eq_def]
      congr
      funext child
      cases child <;> rfl)

private noncomputable def implementation : (width : Nat) → Implementation width
  | 0 => baseImplementation
  | width + 1 => succImplementation width (implementation width)

noncomputable def certification (width : Nat) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure width) (cycleContract width) :=
  implementation width

noncomputable def certified (width : Nat) : Contracts.Cycle.ModuleCycleCertified (ports width) :=
  (certification width).bundle


end Silean.Modules.BinaryToOneHot
