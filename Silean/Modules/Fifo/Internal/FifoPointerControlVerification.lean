import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Modules.Fifo.FifoPointerControl
import Silean.Modules.Equality.EqualityTheorems

/-! Certification machinery for the authored FIFO pointer controller. -/

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
  output
    | .readAddress =>
      [.readSplit => Composition.SignalComponentRule.apply,
        .readAddress => Composition.SignalComponentRule.apply]
    | .writeAddress =>
      [.writeSplit => Composition.SignalComponentRule.apply,
        .writeAddress => Composition.SignalComponentRule.apply]
    | .inputReady =>
      [.readSplit => Composition.SignalComponentRule.apply,
        .writeSplit => Composition.SignalComponentRule.apply,
        .readAddress => Composition.SignalComponentRule.apply,
        .writeAddress => Composition.SignalComponentRule.apply,
        .addressEquality => Equality.Rule.apply,
        .wrapEquality => Primitives.EqRule.apply,
        .wrapDifference => Primitives.NotRule.apply,
        .fullGate => Primitives.AndRule.apply,
        .readyInverter => Primitives.NotRule.apply]
    | .outputValid =>
      [.readSplit => Composition.SignalComponentRule.apply,
        .writeSplit => Composition.SignalComponentRule.apply,
        .readAddress => Composition.SignalComponentRule.apply,
        .writeAddress => Composition.SignalComponentRule.apply,
        .addressEquality => Equality.Rule.apply,
        .wrapEquality => Primitives.EqRule.apply,
        .emptyGate => Primitives.AndRule.apply,
        .validInverter => Primitives.NotRule.apply]
    | .readAdvance =>
      [.readSplit => Composition.SignalComponentRule.apply,
        .writeSplit => Composition.SignalComponentRule.apply,
        .readAddress => Composition.SignalComponentRule.apply,
        .writeAddress => Composition.SignalComponentRule.apply,
        .addressEquality => Equality.Rule.apply,
        .wrapEquality => Primitives.EqRule.apply,
        .emptyGate => Primitives.AndRule.apply,
        .validInverter => Primitives.NotRule.apply,
        .readGate => Primitives.AndRule.apply]
    | .writeAdvance =>
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
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body addressWidth) layerChildren)
      (cycleContract addressWidth)
      (stateCorresponds addressWidth layerChildren) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatches for body addressWidth from
    layerChildren, hierStep, satisfies
  have boundary := satisfies.1
  let readPointer : Pointer addressWidth :=
    fun index => hierStep.inputs .readPointer index
  let writePointer : Pointer addressWidth :=
    fun index => hierStep.inputs .writePointer index
  let readSplit : Pointer addressWidth :=
    fun index => (hierStep.children .readSplit).outputs index
  let writeSplit : Pointer addressWidth :=
    fun index => (hierStep.children .writeSplit).outputs index
  let readAddress : Address addressWidth :=
    (hierStep.children .readAddress).outputs .value
  let writeAddress : Address addressWidth :=
    (hierStep.children .writeAddress).outputs .value
  have readSplitOutputs := (Composition.SignalSplitter.outputRule_holds_iff
    (pointerSplitter addressWidth) _ _ _).mp
      ((childMatches .readSplit).ruleHolds Composition.SignalComponentRule.apply)
  change readSplit = readPointer at readSplitOutputs
  have writeSplitOutputs := (Composition.SignalSplitter.outputRule_holds_iff
    (pointerSplitter addressWidth) _ _ _).mp
      ((childMatches .writeSplit).ruleHolds Composition.SignalComponentRule.apply)
  change writeSplit = writePointer at writeSplitOutputs
  have readAddressOutputs := (Composition.SignalCombiner.outputRule_holds_iff
    (addressCombiner addressWidth) _ _ _).mp
      ((childMatches .readAddress).ruleHolds Composition.SignalComponentRule.apply)
  have writeAddressOutputs := (Composition.SignalCombiner.outputRule_holds_iff
    (addressCombiner addressWidth) _ _ _).mp
      ((childMatches .writeAddress).ruleHolds Composition.SignalComponentRule.apply)
  have readAddressInputs :
      (body addressWidth).wiring.childInputValues hierStep.inputs
        hierStep.childOutputs .readAddress = fun index => readSplit index.castSucc := by
    funext index
    rfl
  have writeAddressInputs :
      (body addressWidth).wiring.childInputValues hierStep.inputs
        hierStep.childOutputs .writeAddress = fun index => writeSplit index.castSucc := by
    funext index
    rfl
  rw [readAddressInputs] at readAddressOutputs
  rw [writeAddressInputs] at writeAddressOutputs
  have readAddressSplit : readAddress = fun index => readSplit index.castSucc := by
    rw [show readAddress = hierStep.childOutputs .readAddress .value by rfl]
    rw [congrFun readAddressOutputs .value]
    rfl
  have writeAddressSplit : writeAddress = fun index => writeSplit index.castSucc := by
    rw [show writeAddress = hierStep.childOutputs .writeAddress .value by rfl]
    rw [congrFun writeAddressOutputs .value]
    rfl
  have readAddressValue : readAddress = pointerAddress readPointer := by
    rw [readAddressSplit, readSplitOutputs]
    rfl
  have writeAddressValue : writeAddress = pointerAddress writePointer := by
    rw [writeAddressSplit, writeSplitOutputs]
    rfl
  have addressEqualityOutput := Equality.result_of_allowed
    (addressType addressWidth) (childMatches .addressEquality).allowed
  change (hierStep.children .addressEquality).outputs .result =
    (addressType addressWidth).equal
      readAddress writeAddress at addressEqualityOutput
  have addressEqualityValue : (hierStep.children .addressEquality).outputs .result =
      addressesEqual readPointer writePointer := by
    rw [addressEqualityOutput, readAddressValue, writeAddressValue]
    rfl
  have wrapEqualityOutput := (Primitives.eqOutputRule_holds_iff _ _ _).mp
    ((childMatches .wrapEquality).ruleHolds Primitives.EqRule.apply)
  change (hierStep.children .wrapEquality).outputs .output =
    SignalType.bit.equal
      (readSplit (Fin.last addressWidth))
      (writeSplit (Fin.last addressWidth)) at wrapEqualityOutput
  have wrapEqualityValue : (hierStep.children .wrapEquality).outputs .output =
      wrapsEqual readPointer writePointer := by
    rw [wrapEqualityOutput, readSplitOutputs, writeSplitOutputs]
    rfl
  have wrapDifferenceOutput := (Primitives.notOutputRule_holds_iff _ _ _).mp
    ((childMatches .wrapDifference).ruleHolds Primitives.NotRule.apply)
  change (hierStep.children .wrapDifference).outputs .output =
    !(hierStep.children .wrapEquality).outputs .output at wrapDifferenceOutput
  have wrapDifferenceValue : (hierStep.children .wrapDifference).outputs .output =
      wrapsDiffer readPointer writePointer := by
    rw [wrapDifferenceOutput, wrapEqualityValue]
    rfl
  have emptyOutput := (Primitives.andOutputRule_holds_iff _ _ _).mp
    ((childMatches .emptyGate).ruleHolds Primitives.AndRule.apply)
  change (hierStep.children .emptyGate).outputs .output =
    ((hierStep.children .addressEquality).outputs .result &&
      (hierStep.children .wrapEquality).outputs .output) at emptyOutput
  have emptyValue : (hierStep.children .emptyGate).outputs .output =
      empty readPointer writePointer := by
    rw [emptyOutput, addressEqualityValue, wrapEqualityValue]
    rfl
  have fullOutput := (Primitives.andOutputRule_holds_iff _ _ _).mp
    ((childMatches .fullGate).ruleHolds Primitives.AndRule.apply)
  change (hierStep.children .fullGate).outputs .output =
    ((hierStep.children .addressEquality).outputs .result &&
      (hierStep.children .wrapDifference).outputs .output) at fullOutput
  have fullValue : (hierStep.children .fullGate).outputs .output =
      full readPointer writePointer := by
    rw [fullOutput, addressEqualityValue, wrapDifferenceValue]
    rfl
  have readyOutput := (Primitives.notOutputRule_holds_iff _ _ _).mp
    ((childMatches .readyInverter).ruleHolds Primitives.NotRule.apply)
  change (hierStep.children .readyInverter).outputs .output =
    !(hierStep.children .fullGate).outputs .output at readyOutput
  have readyValue : (hierStep.children .readyInverter).outputs .output =
      inputReady readPointer writePointer := by
    rw [readyOutput, fullValue]
    rfl
  have validOutput := (Primitives.notOutputRule_holds_iff _ _ _).mp
    ((childMatches .validInverter).ruleHolds Primitives.NotRule.apply)
  change (hierStep.children .validInverter).outputs .output =
    !(hierStep.children .emptyGate).outputs .output at validOutput
  have validValue : (hierStep.children .validInverter).outputs .output =
      outputValid readPointer writePointer := by
    rw [validOutput, emptyValue]
    rfl
  have readOutput := (Primitives.andOutputRule_holds_iff _ _ _).mp
    ((childMatches .readGate).ruleHolds Primitives.AndRule.apply)
  change (hierStep.children .readGate).outputs .output =
    ((hierStep.children .validInverter).outputs .output && hierStep.inputs .outputReady) at readOutput
  have readValue : (hierStep.children .readGate).outputs .output =
      readAdvance readPointer writePointer
        (hierStep.inputs .outputReady) := by
    rw [readOutput, validValue]
    rfl
  have writeOutput := (Primitives.andOutputRule_holds_iff _ _ _).mp
    ((childMatches .writeGate).ruleHolds Primitives.AndRule.apply)
  change (hierStep.children .writeGate).outputs .output =
    (hierStep.inputs .inputValid && (hierStep.children .readyInverter).outputs .output) at writeOutput
  have writeValue : (hierStep.children .writeGate).outputs .output =
      writeAdvance readPointer writePointer
        (hierStep.inputs .inputValid) := by
    rw [writeOutput, readyValue]
    rfl
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    · rw [readAddressRule_holds_iff]
      change hierStep.outputs .readAddress = pointerAddress readPointer
      exact (boundary .readAddress).trans readAddressValue
    · rw [writeAddressRule_holds_iff]
      change hierStep.outputs .writeAddress = pointerAddress writePointer
      exact (boundary .writeAddress).trans writeAddressValue
    · rw [inputReadyRule_holds_iff]
      change hierStep.outputs .inputReady = inputReady readPointer writePointer
      exact (boundary .inputReady).trans readyValue
    · rw [outputValidRule_holds_iff]
      change hierStep.outputs .outputValid = outputValid readPointer writePointer
      exact (boundary .outputValid).trans validValue
    · rw [readAdvanceRule_holds_iff]
      change hierStep.outputs .readAdvance =
        readAdvance readPointer writePointer (hierStep.inputs .outputReady)
      exact (boundary .readAdvance).trans readValue
    · rw [writeAdvanceRule_holds_iff]
      change hierStep.outputs .writeAdvance =
        writeAdvance readPointer writePointer (hierStep.inputs .inputValid)
      exact (boundary .writeAdvance).trans writeValue
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
