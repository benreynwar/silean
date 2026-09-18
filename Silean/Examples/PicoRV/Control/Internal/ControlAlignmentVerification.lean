import Silean.Examples.PicoRV.Control.ControlAlignment
import Silean.Examples.PicoRV.Control.ControlBitLaws
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.EqualsConstant.EqualsConstantTheorems
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems
import Silean.Primitives.And
import Silean.Primitives.Or

namespace Silean.Examples.PicoRV.Control.Alignment

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  inputsFields := Modules.NamedTupleSplitter.certification
    ControlInputs.signalMap,
  stateFields := Modules.NamedTupleSplitter.certification stateMap,
  op1Bits := wordSplitter.certified.certification,
  pcBits := wordSplitter.certified.certification,
  sizeIsWord := Modules.EqualsConstant.certification (.vector 2 .bit)
    (twoBitsOfNat 0),
  sizeIsHalf := Modules.EqualsConstant.certification (.vector 2 .bit)
    (twoBitsOfNat 1),
  dataCommand := Primitives.orCertified.certification,
  op1Low := Primitives.orCertified.certification,
  pcLow := Primitives.orCertified.certification,
  wordMisaligned := Primitives.andCertified.certification,
  halfMisaligned := Primitives.andCertified.certification,
  sizeMisaligned := Primitives.orCertified.certification,
  dataMisaligned := Primitives.andCertified.certification,
  instructionMisaligned := Primitives.andCertified.certification

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .apply => [
        .inputsFields => Modules.NamedTupleSplitter.Rule.apply,
        .stateFields => Modules.NamedTupleSplitter.Rule.apply,
        {.op1Bits, .pcBits} => Composition.SignalComponentRule.apply,
        {.sizeIsWord, .sizeIsHalf} => Modules.EqualsConstant.Rule.apply,
        {.dataCommand, .op1Low, .pcLow} => Primitives.OrRule.apply,
        {.wordMisaligned, .halfMisaligned} => Primitives.AndRule.apply,
        .sizeMisaligned => Primitives.OrRule.apply,
        {.dataMisaligned, .instructionMisaligned} => Primitives.AndRule.apply]
  state := []

private theorem splitValue_eq_unpack (signals : SignalMap.{0})
    (value : signals.tupleType.Denote) :
    Modules.NamedTupleSplitter.splitValue signals value = signals.unpack value := by
  calc
    Modules.NamedTupleSplitter.splitValue signals value =
        Modules.NamedTupleSplitter.splitValue signals
          (signals.pack (signals.unpack value)) := by
      rw [signals.pack_unpack]
    _ = signals.unpack value :=
      Modules.NamedTupleSplitter.splitValue_pack signals _

def structuralData (inputs : Inputs) (current : stateMap.Values) : Bool :=
  ((current .mem_do_rdata : Bool) || current .mem_do_wdata) &&
    ((decide (wordSize current = 0) &&
        (inputs.reg_op1 0 || inputs.reg_op1 1)) ||
      (decide (wordSize current = 1) && inputs.reg_op1 0))

def structuralInstruction (inputs : Inputs)
    (current : stateMap.Values) : Bool :=
  (current .mem_do_rinst : Bool) && (inputs.reg_pc 0 || inputs.reg_pc 1)

theorem structuralData_eq_dataMisaligned (inputs : Inputs)
    (current : stateMap.Values) :
    structuralData inputs current = dataMisaligned inputs current := by
  unfold structuralData dataMisaligned
  rw [word_mod_four_ne_zero inputs.reg_op1]

theorem structuralInstruction_eq_instructionMisaligned (inputs : Inputs)
    (current : stateMap.Values) :
    structuralInstruction inputs current = instructionMisaligned inputs current := by
  unfold structuralInstruction instructionMisaligned
  rw [word_mod_four_ne_zero inputs.reg_pc]

section Certification

variable (layerChildren : ChildStructures body childContracts)

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (Contracts.Cycle.Certification.Layer.moduleStructure
      body layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for body from
    layerChildren, hierStep, satisfies

  let controlInputs := Inputs.unpack (hierStep.inputs .inputs)
  let current := stateMap.unpack (hierStep.inputs .current)

  have inputsFieldsValue : hierStep.childOutputs .inputsFields =
      ControlInputs.signalMap.unpack (hierStep.inputs .inputs) := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      ControlInputs.signalMap _ _ _).mp
      ((childMatch .inputsFields).ruleHolds Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    change hierStep.childOutputs .inputsFields =
      Modules.NamedTupleSplitter.splitValue ControlInputs.signalMap
        (hierStep.inputs .inputs) at equation
    exact equation.trans (splitValue_eq_unpack _ _)

  have stateFieldsValue : hierStep.childOutputs .stateFields = current := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .stateFields).ruleHolds Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    change hierStep.childOutputs .stateFields =
      Modules.NamedTupleSplitter.splitValue stateMap
        (hierStep.inputs .current) at equation
    exact equation.trans ((splitValue_eq_unpack _ _).trans (by rfl))

  have op1Split := (wordSplitter.outputRule_holds_iff _ _ _).mp
    ((childMatch .op1Bits).ruleHolds Composition.SignalComponentRule.apply)
  have pcSplit := (wordSplitter.outputRule_holds_iff _ _ _).mp
    ((childMatch .pcBits).ruleHolds Composition.SignalComponentRule.apply)

  have op1Field : hierStep.childOutputs .inputsFields .reg_op1 =
      controlInputs.reg_op1 := by
    rw [inputsFieldsValue]
    rfl

  have pcField : hierStep.childOutputs .inputsFields .reg_pc =
      controlInputs.reg_pc := by
    rw [inputsFieldsValue]
    rfl

  have op1Bit (index : Fin 32) :
      hierStep.childOutputs .op1Bits index = controlInputs.reg_op1 index := by
    have equation := congrFun op1Split index
    have wired : hierStep.childOutputs .op1Bits index =
        hierStep.childOutputs .inputsFields .reg_op1 index := by
      simpa [Composition.SignalSplitter.outputValues, wordSplitter,
        body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value] using equation
    rw [wired, congrFun op1Field index]

  have pcBit (index : Fin 32) :
      hierStep.childOutputs .pcBits index = controlInputs.reg_pc index := by
    have equation := congrFun pcSplit index
    have wired : hierStep.childOutputs .pcBits index =
        hierStep.childOutputs .inputsFields .reg_pc index := by
      simpa [Composition.SignalSplitter.outputValues, wordSplitter,
        body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value] using equation
    rw [wired, congrFun pcField index]

  have sizeIsWordValue : hierStep.childOutputs .sizeIsWord .result =
      decide (wordSize current = 0) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 2 .bit) (twoBitsOfNat 0) _ _ _).mp
      ((childMatch .sizeIsWord).ruleHolds Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans <| (congrArg
      (fun bits => (SignalType.vector 2 .bit).equal bits (twoBitsOfNat 0))
      (congrFun stateFieldsValue .mem_wordsize)).trans (by
        rw [show twoBitsOfNat 0 = BitVector.ofNat 2 0 by rfl]
        exact signalTypeEqual_ofNat 2 0 (current .mem_wordsize) (by decide))

  have sizeIsHalfValue : hierStep.childOutputs .sizeIsHalf .result =
      decide (wordSize current = 1) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 2 .bit) (twoBitsOfNat 1) _ _ _).mp
      ((childMatch .sizeIsHalf).ruleHolds Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans <| (congrArg
      (fun bits => (SignalType.vector 2 .bit).equal bits (twoBitsOfNat 1))
      (congrFun stateFieldsValue .mem_wordsize)).trans (by
        rw [show twoBitsOfNat 1 = BitVector.ofNat 2 1 by rfl]
        exact signalTypeEqual_ofNat 2 1 (current .mem_wordsize) (by decide))

  have dataCommandValue : hierStep.childOutputs .dataCommand .output =
      ((current .mem_do_rdata : Bool) || current .mem_do_wdata) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .dataCommand).ruleHolds Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (apply₂_congr Bool.or
      (congrFun stateFieldsValue .mem_do_rdata)
      (congrFun stateFieldsValue .mem_do_wdata))

  have op1LowValue : hierStep.childOutputs .op1Low .output =
      (controlInputs.reg_op1 0 || controlInputs.reg_op1 1) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .op1Low).ruleHolds Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (apply₂_congr Bool.or (op1Bit 0) (op1Bit 1))

  have pcLowValue : hierStep.childOutputs .pcLow .output =
      (controlInputs.reg_pc 0 || controlInputs.reg_pc 1) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .pcLow).ruleHolds Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (apply₂_congr Bool.or (pcBit 0) (pcBit 1))

  have wordMisalignedValue : hierStep.childOutputs .wordMisaligned .output =
      (decide (wordSize current = 0) &&
        (controlInputs.reg_op1 0 || controlInputs.reg_op1 1)) := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .wordMisaligned).ruleHolds Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (apply₂_congr Bool.and
      sizeIsWordValue op1LowValue)

  have halfMisalignedValue : hierStep.childOutputs .halfMisaligned .output =
      (decide (wordSize current = 1) && controlInputs.reg_op1 0) := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .halfMisaligned).ruleHolds Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (apply₂_congr Bool.and
      sizeIsHalfValue (op1Bit 0))

  have sizeMisalignedValue : hierStep.childOutputs .sizeMisaligned .output =
      ((decide (wordSize current = 0) &&
          (controlInputs.reg_op1 0 || controlInputs.reg_op1 1)) ||
        (decide (wordSize current = 1) && controlInputs.reg_op1 0)) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .sizeMisaligned).ruleHolds Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (apply₂_congr Bool.or
      wordMisalignedValue halfMisalignedValue)

  have dataValue : hierStep.childOutputs .dataMisaligned .output =
      structuralData controlInputs current := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .dataMisaligned).ruleHolds Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact (equation.trans (apply₂_congr Bool.and
      dataCommandValue sizeMisalignedValue)).trans (by rfl)

  have instructionValue : hierStep.childOutputs .instructionMisaligned .output =
      structuralInstruction controlInputs current := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .instructionMisaligned).ruleHolds Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact (equation.trans (apply₂_congr Bool.and
      (congrFun stateFieldsValue .mem_do_rinst) pcLowValue)).trans (by rfl)

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    dsimp only
    funext output
    cases output
    · rw [show hierStep.outputs .data =
          hierStep.childOutputs .dataMisaligned .output by
        exact satisfies.1 .data]
      rw [dataValue, structuralData_eq_dataMisaligned]
      rfl
    · rw [show hierStep.outputs .instruction =
          hierStep.childOutputs .instructionMisaligned .output by
        exact satisfies.1 .instruction]
      rw [instructionValue, structuralInstruction_eq_instructionMisaligned]
      rfl
  · rfl

end Certification

module_cycle_certification certification for moduleStructure via body
    with childContracts implementing cycleContract where
  schedules := derivedRuleSchedules,
  structuralChildren := structuralChildren,
  certifiedChildren := certifiedChildren,
  structuresMatch := certifiedChildren_moduleStructure,
  stateCorresponds := stateCorresponds,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements

end Silean.Examples.PicoRV.Control.Alignment
