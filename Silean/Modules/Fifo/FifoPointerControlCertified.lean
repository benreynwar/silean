import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Modules.Fifo.FifoPointerControl

namespace Silean.Modules.Fifo.PointerControl

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts (addressWidth : Nat)
    for body addressWidth where
  readSplit := (pointerSplitter addressWidth).certified.certification,
  writeSplit := (pointerSplitter addressWidth).certified.certification,
  readAddress := (addressCombiner addressWidth).certified.certification,
  writeAddress := (addressCombiner addressWidth).certified.certification,
  addressEquality := Equality.certification (addressType addressWidth),
  wrapEquality := Primitives.eqCertified.certification,
  wrapDifference := Primitives.notCertified.certification,
  emptyGate := Primitives.andCertified.certification,
  fullGate := Primitives.andCertified.certification,
  readyInverter := Primitives.notCertified.certification,
  validInverter := Primitives.notCertified.certification,
  readGate := Primitives.andCertified.certification,
  writeGate := Primitives.andCertified.certification

module_rule_schedules derivedRuleSchedules (addressWidth : Nat)
    for body addressWidth with childContracts addressWidth
    implementing cycleContract addressWidth where
  output | .apply =>
    [.readSplit => Composition.SignalComponentRule.apply,
      .writeSplit => Composition.SignalComponentRule.apply,
      .readAddress => Composition.SignalComponentRule.apply,
      .writeAddress => Composition.SignalComponentRule.apply,
      .addressEquality => Equality.Rule.apply,
      .wrapEquality => Primitives.EqRule.apply,
      .wrapDifference => Primitives.NotRule.apply,
      .emptyGate => Primitives.AndRule.apply,
      .fullGate => Primitives.AndRule.apply,
      .readyInverter => Primitives.NotRule.apply,
      .validInverter => Primitives.NotRule.apply,
      .readGate => Primitives.AndRule.apply,
      .writeGate => Primitives.AndRule.apply]
  state := []

section LayerCertification

variable (addressWidth : Nat)
  (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
    (body addressWidth) (childContracts addressWidth))

private def stateCorresponds (_ : (cycleContract addressWidth).state.Values)
    (_ : (Contracts.Cycle.Certification.Layer.moduleStructure
      (body addressWidth) layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body addressWidth) layerChildren)
      (cycleContract addressWidth)
      (stateCorresponds addressWidth layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have childMatches :=
    Contracts.Cycle.Certification.Layer.childSolutionsMatchContracts_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies
      (fun child => by cases child <;> exact SignalMap.emptyValues)
      (by intro child; cases child <;>
        change Subsingleton emptySignalMap.Values <;> infer_instance)
  rcases proposal with ⟨outputs, proposals⟩
  have boundary := satisfies.1
  have readSplitOutputs := (Composition.SignalSplitter.outputRule_holds_iff
    (pointerSplitter addressWidth) _ _ _).mp
      ((childMatches .readSplit).1.1 Composition.SignalComponentRule.apply)
  have writeSplitOutputs := (Composition.SignalSplitter.outputRule_holds_iff
    (pointerSplitter addressWidth) _ _ _).mp
      ((childMatches .writeSplit).1.1 Composition.SignalComponentRule.apply)
  have readAddressOutputs := (Composition.SignalCombiner.outputRule_holds_iff
    (addressCombiner addressWidth) _ _ _).mp
      ((childMatches .readAddress).1.1 Composition.SignalComponentRule.apply)
  have writeAddressOutputs := (Composition.SignalCombiner.outputRule_holds_iff
    (addressCombiner addressWidth) _ _ _).mp
      ((childMatches .writeAddress).1.1 Composition.SignalComponentRule.apply)
  have readAddressValue : (proposals .readAddress).outputs .value =
      pointerAddress (inputs .readPointer) := by
    rw [congrFun readAddressOutputs .value]
    funext index
    change (proposals .readSplit).outputs index.castSucc =
      inputs .readPointer index.castSucc
    rw [congrFun readSplitOutputs index.castSucc]
    rfl
  have writeAddressValue : (proposals .writeAddress).outputs .value =
      pointerAddress (inputs .writePointer) := by
    rw [congrFun writeAddressOutputs .value]
    funext index
    change (proposals .writeSplit).outputs index.castSucc =
      inputs .writePointer index.castSucc
    rw [congrFun writeSplitOutputs index.castSucc]
    rfl
  have addressEqualityOutput :=
    (Equality.outputRule_holds_iff (addressType addressWidth) _ _ _).mp
      ((childMatches .addressEquality).1.1 Equality.Rule.apply)
  change (proposals .addressEquality).outputs .result =
    (addressType addressWidth).equal
      ((proposals .readAddress).outputs .value)
      ((proposals .writeAddress).outputs .value) at addressEqualityOutput
  have addressEqualityValue : (proposals .addressEquality).outputs .result =
      addressesEqual (inputs .readPointer) (inputs .writePointer) := by
    rw [addressEqualityOutput, readAddressValue, writeAddressValue]
    rfl
  have wrapEqualityOutput := (Primitives.eqOutputRule_holds_iff _ _ _).mp
    ((childMatches .wrapEquality).1.1 Primitives.EqRule.apply)
  change (proposals .wrapEquality).outputs .output =
    SignalType.bit.equal
      ((proposals .readSplit).outputs (Fin.last addressWidth))
      ((proposals .writeSplit).outputs (Fin.last addressWidth)) at wrapEqualityOutput
  have wrapEqualityValue : (proposals .wrapEquality).outputs .output =
      wrapsEqual (inputs .readPointer) (inputs .writePointer) := by
    rw [wrapEqualityOutput,
      congrFun readSplitOutputs (Fin.last addressWidth),
      congrFun writeSplitOutputs (Fin.last addressWidth)]
    rfl
  have wrapDifferenceOutput := (Primitives.notOutputRule_holds_iff _ _ _).mp
    ((childMatches .wrapDifference).1.1 Primitives.NotRule.apply)
  change (proposals .wrapDifference).outputs .output =
    !(proposals .wrapEquality).outputs .output at wrapDifferenceOutput
  have wrapDifferenceValue : (proposals .wrapDifference).outputs .output =
      wrapsDiffer (inputs .readPointer) (inputs .writePointer) := by
    rw [wrapDifferenceOutput, wrapEqualityValue]
    rfl
  have emptyOutput := (Primitives.andOutputRule_holds_iff _ _ _).mp
    ((childMatches .emptyGate).1.1 Primitives.AndRule.apply)
  change (proposals .emptyGate).outputs .output =
    ((proposals .addressEquality).outputs .result &&
      (proposals .wrapEquality).outputs .output) at emptyOutput
  have emptyValue : (proposals .emptyGate).outputs .output =
      empty (inputs .readPointer) (inputs .writePointer) := by
    rw [emptyOutput, addressEqualityValue, wrapEqualityValue]
    rfl
  have fullOutput := (Primitives.andOutputRule_holds_iff _ _ _).mp
    ((childMatches .fullGate).1.1 Primitives.AndRule.apply)
  change (proposals .fullGate).outputs .output =
    ((proposals .addressEquality).outputs .result &&
      (proposals .wrapDifference).outputs .output) at fullOutput
  have fullValue : (proposals .fullGate).outputs .output =
      full (inputs .readPointer) (inputs .writePointer) := by
    rw [fullOutput, addressEqualityValue, wrapDifferenceValue]
    rfl
  have readyOutput := (Primitives.notOutputRule_holds_iff _ _ _).mp
    ((childMatches .readyInverter).1.1 Primitives.NotRule.apply)
  change (proposals .readyInverter).outputs .output =
    !(proposals .fullGate).outputs .output at readyOutput
  have readyValue : (proposals .readyInverter).outputs .output =
      inputReady (inputs .readPointer) (inputs .writePointer) := by
    rw [readyOutput, fullValue]
    rfl
  have validOutput := (Primitives.notOutputRule_holds_iff _ _ _).mp
    ((childMatches .validInverter).1.1 Primitives.NotRule.apply)
  change (proposals .validInverter).outputs .output =
    !(proposals .emptyGate).outputs .output at validOutput
  have validValue : (proposals .validInverter).outputs .output =
      outputValid (inputs .readPointer) (inputs .writePointer) := by
    rw [validOutput, emptyValue]
    rfl
  have readOutput := (Primitives.andOutputRule_holds_iff _ _ _).mp
    ((childMatches .readGate).1.1 Primitives.AndRule.apply)
  change (proposals .readGate).outputs .output =
    ((proposals .validInverter).outputs .output && inputs .outputReady) at readOutput
  have readValue : (proposals .readGate).outputs .output =
      readAdvance (inputs .readPointer) (inputs .writePointer)
        (inputs .outputReady) := by
    rw [readOutput, validValue]
    rfl
  have writeOutput := (Primitives.andOutputRule_holds_iff _ _ _).mp
    ((childMatches .writeGate).1.1 Primitives.AndRule.apply)
  change (proposals .writeGate).outputs .output =
    (inputs .inputValid && (proposals .readyInverter).outputs .output) at writeOutput
  have writeValue : (proposals .writeGate).outputs .output =
      writeAdvance (inputs .readPointer) (inputs .writePointer)
        (inputs .inputValid) := by
    rw [writeOutput, readyValue]
    rfl
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    change (outputRule addressWidth).Holds inputs contractState outputs
    rw [outputRule_holds_iff]
    exact ⟨(boundary .readAddress).trans readAddressValue,
      (boundary .writeAddress).trans writeAddressValue,
      (boundary .inputReady).trans readyValue,
      (boundary .outputValid).trans validValue,
      (boundary .readAdvance).trans readValue,
      (boundary .writeAdvance).trans writeValue⟩
  · rfl

end LayerCertification
/- The pointer-control wiring implements its combinational contract for any
children satisfying the declared adapter, equality, and bit-logic contracts. -/
module_cycle_certification certification (addressWidth : Nat)
    for moduleStructure addressWidth via body addressWidth
    with childContracts addressWidth implementing cycleContract addressWidth where
  schedules := derivedRuleSchedules addressWidth,
  structuralChildren := structuralChildren addressWidth,
  certifiedChildren := certifiedChildren addressWidth,
  structuresMatch := certifiedChildren_moduleStructure addressWidth,
  stateCorresponds := stateCorresponds addressWidth,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements addressWidth

end Silean.Modules.Fifo.PointerControl
