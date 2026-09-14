import Silean.Examples.PicoRV.Control.ControlAlignment
import Silean.Examples.PicoRV.Control.ControlBitLaws
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.EqualsConstant.EqualsConstantCertified
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified
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

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (_ : emptySignalMap.Values)
    (_ : (certificationStructure layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.Implements (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  derive_empty_state_child_matches childMatch from
    layerChildren, inputs, structuralState, proposal, satisfies

  let controlInputs := Inputs.unpack (inputs .inputs)
  let current := stateMap.unpack (inputs .current)

  have inputsFieldsValue : (proposal.2 .inputsFields).outputs =
      ControlInputs.signalMap.unpack (inputs .inputs) := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      ControlInputs.signalMap _ _ _).mp
      ((childMatch .inputsFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [splitValue_eq_unpack] using equation

  have stateFieldsValue : (proposal.2 .stateFields).outputs = current := by
    have equation := (Modules.NamedTupleSplitter.outputRule_holds_iff
      stateMap _ _ _).mp
      ((childMatch .stateFields).1.1 Modules.NamedTupleSplitter.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    simpa [splitValue_eq_unpack, current] using equation

  have op1Split := (wordSplitter.outputRule_holds_iff _ _ _).mp
    ((childMatch .op1Bits).1.1 Composition.SignalComponentRule.apply)
  have pcSplit := (wordSplitter.outputRule_holds_iff _ _ _).mp
    ((childMatch .pcBits).1.1 Composition.SignalComponentRule.apply)

  have op1Field : (proposal.2 .inputsFields).outputs .reg_op1 =
      controlInputs.reg_op1 := by
    rw [inputsFieldsValue]
    rfl

  have pcField : (proposal.2 .inputsFields).outputs .reg_pc =
      controlInputs.reg_pc := by
    rw [inputsFieldsValue]
    rfl

  have op1Bit (index : Fin 32) :
      (proposal.2 .op1Bits).outputs index = controlInputs.reg_op1 index := by
    have equation := congrFun op1Split index
    have wired : (proposal.2 .op1Bits).outputs index =
        (proposal.2 .inputsFields).outputs .reg_op1 index := by
      simpa [Composition.SignalSplitter.outputValues, wordSplitter,
        ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value] using equation
    rw [wired, congrFun op1Field index]

  have pcBit (index : Fin 32) :
      (proposal.2 .pcBits).outputs index = controlInputs.reg_pc index := by
    have equation := congrFun pcSplit index
    have wired : (proposal.2 .pcBits).outputs index =
        (proposal.2 .inputsFields).outputs .reg_pc index := by
      simpa [Composition.SignalSplitter.outputValues, wordSplitter,
        ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value] using equation
    rw [wired, congrFun pcField index]

  have sizeIsWordValue : (proposal.2 .sizeIsWord).outputs .result =
      decide (wordSize current = 0) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 2 .bit) (twoBitsOfNat 0) _ _ _).mp
      ((childMatch .sizeIsWord).1.1 Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [stateFieldsValue] at equation
    rw [equation]
    change (SignalType.vector 2 .bit).equal
      (current .mem_wordsize) (twoBitsOfNat 0) =
        decide (wordSize current = 0)
    rw [show twoBitsOfNat 0 = BitVector.ofNat 2 0 by rfl]
    exact signalTypeEqual_ofNat 2 0 (current .mem_wordsize) (by decide)

  have sizeIsHalfValue : (proposal.2 .sizeIsHalf).outputs .result =
      decide (wordSize current = 1) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 2 .bit) (twoBitsOfNat 1) _ _ _).mp
      ((childMatch .sizeIsHalf).1.1 Modules.EqualsConstant.Rule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [stateFieldsValue] at equation
    rw [equation]
    change (SignalType.vector 2 .bit).equal
      (current .mem_wordsize) (twoBitsOfNat 1) =
        decide (wordSize current = 1)
    rw [show twoBitsOfNat 1 = BitVector.ofNat 2 1 by rfl]
    exact signalTypeEqual_ofNat 2 1 (current .mem_wordsize) (by decide)

  have dataCommandValue : (proposal.2 .dataCommand).outputs .output =
      ((current .mem_do_rdata : Bool) || current .mem_do_wdata) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .dataCommand).1.1 Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [stateFieldsValue] at equation
    exact equation

  have op1LowValue : (proposal.2 .op1Low).outputs .output =
      (controlInputs.reg_op1 0 || controlInputs.reg_op1 1) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .op1Low).1.1 Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [op1Bit 0, op1Bit 1] at equation
    exact equation

  have pcLowValue : (proposal.2 .pcLow).outputs .output =
      (controlInputs.reg_pc 0 || controlInputs.reg_pc 1) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .pcLow).1.1 Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [pcBit 0, pcBit 1] at equation
    exact equation

  have wordMisalignedValue : (proposal.2 .wordMisaligned).outputs .output =
      (decide (wordSize current = 0) &&
        (controlInputs.reg_op1 0 || controlInputs.reg_op1 1)) := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .wordMisaligned).1.1 Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [sizeIsWordValue, op1LowValue] at equation
    exact equation

  have halfMisalignedValue : (proposal.2 .halfMisaligned).outputs .output =
      (decide (wordSize current = 1) && controlInputs.reg_op1 0) := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .halfMisaligned).1.1 Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [sizeIsHalfValue, op1Bit 0] at equation
    exact equation

  have sizeMisalignedValue : (proposal.2 .sizeMisaligned).outputs .output =
      ((decide (wordSize current = 0) &&
          (controlInputs.reg_op1 0 || controlInputs.reg_op1 1)) ||
        (decide (wordSize current = 1) && controlInputs.reg_op1 0)) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .sizeMisaligned).1.1 Primitives.OrRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [wordMisalignedValue, halfMisalignedValue] at equation
    exact equation

  have dataValue : (proposal.2 .dataMisaligned).outputs .output =
      structuralData controlInputs current := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .dataMisaligned).1.1 Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [dataCommandValue, sizeMisalignedValue] at equation
    exact equation

  have instructionValue : (proposal.2 .instructionMisaligned).outputs .output =
      structuralInstruction controlInputs current := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((childMatch .instructionMisaligned).1.1 Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    rw [stateFieldsValue, pcLowValue] at equation
    exact equation

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    funext output
    cases output
    · rw [show proposal.outputs .data =
          (proposal.2 .dataMisaligned).outputs .output by
        exact satisfies.1 .data]
      rw [dataValue, structuralData_eq_dataMisaligned]
      rfl
    · rw [show proposal.outputs .instruction =
          (proposal.2 .instructionMisaligned).outputs .output by
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

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.Control.Alignment
