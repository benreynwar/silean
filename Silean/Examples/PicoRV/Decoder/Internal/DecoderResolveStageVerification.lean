import Silean.Examples.PicoRV.Decoder.DecoderResolveStageStructure
import Silean.Examples.PicoRV.Decoder.DecoderImmediateTheorems
import Silean.Examples.PicoRV.Decoder.DecoderInstructionMatchTheorems
import Silean.Examples.PicoRV.Decoder.DecoderInstructionSummaryTheorems
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.EnabledRegister.EnabledRegisterTheorems
import Silean.Modules.EnabledResetRegister.EnabledResetRegisterTheorems
import Silean.Modules.Register.RegisterTheorems
import Silean.Modules.ResetRegister.ResetRegisterTheorems
import Silean.Modules.Mux.MuxTheorems
import Silean.Modules.Constant.Constant
import Silean.Primitives.Not

/-! Internal schedules, grouped state correspondence, and structural
certification for the registered decoder resolve stage. -/

namespace Silean.Examples.PicoRV.Decoder.ResolveStage

open Silean
open Silean.Authoring
open Silean.Examples.PicoRV.Decoder
open Contracts.Cycle.Certification.Layer

/-! All three combinational decoder children—instruction matching, immediate
decoding, and instruction summaries—have concrete certified structures. -/

module_child_certifications childContracts for body where
  pseudoInverter := Primitives.notCertified.certification,
  triggerEnable := Primitives.andCertified.certification,
  resetInverter := Primitives.notCertified.certification,
  instructionMatch := InstructionMatch.Structure.certification,
  immediate := Immediate.certification,
  instructionSummary := InstructionSummary.Structure.certification,
  resetMatchNext := resetMatchCombiner.certified.certification,
  retainedMatchNext := retainedMatchCombiner.certified.certification,
  ordinarySummaryNext := ordinarySummaryCombiner.certified.certification,
  resetMatchStorage := Modules.EnabledResetRegister.certification
    resetMatchType falseResetMatches,
  retainedMatchStorage := Modules.EnabledRegister.certification retainedMatchType,
  immediateStorage := Modules.EnabledRegister.certification immediateType,
  ordinarySummaryStorage := Modules.Register.certification ordinarySummaryType,
  addSubSummaryStorage := Modules.Register.certification .bit,
  compareStorage := Modules.ResetRegister.certification .bit false,
  immediateSelection := Modules.Mux.certification immediateType,
  addSubSummarySelection := Modules.Mux.certification .bit,
  compareSelection := Modules.Mux.certification .bit,
  resetMatchOutputs := resetMatchSplitter.certified.certification,
  retainedMatchOutputs := retainedMatchSplitter.certified.certification,
  ordinarySummaryOutputs := ordinarySummarySplitter.certified.certification,
  falseValue := Modules.Constant.certification .bit false

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .outputs => [.resetMatchStorage => Modules.EnabledResetRegister.Rule.observe,
      .retainedMatchStorage => Modules.EnabledRegister.Rule.observe,
      .immediateStorage => Modules.EnabledRegister.Rule.observe,
      .ordinarySummaryStorage => Primitives.RegisterRule.observe,
      .addSubSummaryStorage => Primitives.RegisterRule.observe,
      .compareStorage => Modules.ResetRegister.Rule.observe,
      .resetMatchOutputs => Composition.SignalComponentRule.apply,
      .retainedMatchOutputs => Composition.SignalComponentRule.apply,
      .ordinarySummaryOutputs => Composition.SignalComponentRule.apply,
      .instructionSummary => InstructionSummary.Rule.trap]
  state := [.resetMatchStorage => Modules.EnabledResetRegister.Rule.observe,
    .retainedMatchStorage => Modules.EnabledRegister.Rule.observe,
    .immediateStorage => Modules.EnabledRegister.Rule.observe,
    .ordinarySummaryStorage => Primitives.RegisterRule.observe,
    .addSubSummaryStorage => Primitives.RegisterRule.observe,
    .compareStorage => Modules.ResetRegister.Rule.observe,
    .resetMatchOutputs => Composition.SignalComponentRule.apply,
    .retainedMatchOutputs => Composition.SignalComponentRule.apply,
    .ordinarySummaryOutputs => Composition.SignalComponentRule.apply,
    .pseudoInverter => Primitives.NotRule.apply,
    .triggerEnable => Primitives.AndRule.apply,
    .resetInverter => Primitives.NotRule.apply,
    .instructionMatch => InstructionMatch.Rule.apply,
    .immediate => Immediate.Rule.apply,
    .instructionSummary => InstructionSummary.Rule.summaries,
    .resetMatchNext => Composition.SignalComponentRule.apply,
    .retainedMatchNext => Composition.SignalComponentRule.apply,
    .ordinarySummaryNext => Composition.SignalComponentRule.apply,
    .falseValue => Primitives.ConstantRule.apply,
    .immediateSelection => Modules.Mux.Rule.select,
    .addSubSummarySelection => Modules.Mux.Rule.select,
    .compareSelection => Modules.Mux.Rule.select]

/-! ## Cycle certification

The contract names all 45 logical decoder registers individually. The
structure stores the same values in six aggregate children. `storageState`
is the proof-only boundary between those views; it is not part of the emitted
hardware.
-/

private def storageState
    (resetMatches : Fin 23 → Bool)
    (retainedMatches : Fin 15 → Bool)
    (immediate : Word)
    (ordinarySummaries : Fin 4 → Bool)
    (addSubSummary compare : Bool) : stateMap.Values
  | .instr_beq => resetMatches 0
  | .instr_bne => resetMatches 1
  | .instr_blt => resetMatches 2
  | .instr_bge => resetMatches 3
  | .instr_bltu => resetMatches 4
  | .instr_bgeu => resetMatches 5
  | .instr_lb => retainedMatches 0
  | .instr_lh => retainedMatches 1
  | .instr_lw => retainedMatches 2
  | .instr_lbu => retainedMatches 3
  | .instr_lhu => retainedMatches 4
  | .instr_sb => retainedMatches 5
  | .instr_sh => retainedMatches 6
  | .instr_sw => retainedMatches 7
  | .instr_addi => resetMatches 6
  | .instr_slti => resetMatches 7
  | .instr_sltiu => resetMatches 8
  | .instr_xori => resetMatches 9
  | .instr_ori => resetMatches 10
  | .instr_andi => resetMatches 11
  | .instr_slli => retainedMatches 8
  | .instr_srli => retainedMatches 9
  | .instr_srai => retainedMatches 10
  | .instr_add => resetMatches 12
  | .instr_sub => resetMatches 13
  | .instr_sll => resetMatches 14
  | .instr_slt => resetMatches 15
  | .instr_sltu => resetMatches 16
  | .instr_xor => resetMatches 17
  | .instr_srl => resetMatches 18
  | .instr_sra => resetMatches 19
  | .instr_or => resetMatches 20
  | .instr_and => resetMatches 21
  | .instr_ecall_ebreak => retainedMatches 11
  | .instr_fence => resetMatches 22
  | .decoded_imm => immediate
  | .is_lui_auipc_jal => ordinarySummaries 0
  | .is_slli_srli_srai => retainedMatches 12
  | .is_jalr_addi_slti_sltiu_xori_ori_andi => retainedMatches 13
  | .is_sll_srl_sra => retainedMatches 14
  | .is_lui_auipc_jal_jalr_addi_add_sub => addSubSummary
  | .is_slti_blt_slt => ordinarySummaries 1
  | .is_sltiu_bltu_sltu => ordinarySummaries 2
  | .is_lbu_lhu_lw => ordinarySummaries 3
  | .is_compare => compare

private abbrev instructionMatchBit := InstructionMatch.bitValue

private abbrev instructionSummaryBit := InstructionSummary.bitValue

private theorem signalType_subst_eq_mp {sourceType targetType : SignalType}
    (equal : sourceType = targetType) (value : sourceType.Denote) :
    equal ▸ value = Eq.mp (congrArg SignalType.Denote equal) value := by
  cases equal
  rfl

private def summaryInputsOf (inputs : Inputs) (resetMatches : Fin 23 → Bool)
    (retainedMatches : Fin 15 → Bool) : InstructionSummary.Inputs where
  instr_lui := inputs.instr_lui
  instr_auipc := inputs.instr_auipc
  instr_jal := inputs.instr_jal
  instr_jalr := inputs.instr_jalr
  is_beq_bne_blt_bge_bltu_bgeu := inputs.is_beq_bne_blt_bge_bltu_bgeu
  matched
    | .instr_beq => resetMatches 0 | .instr_bne => resetMatches 1
    | .instr_blt => resetMatches 2 | .instr_bge => resetMatches 3
    | .instr_bltu => resetMatches 4 | .instr_bgeu => resetMatches 5
    | .instr_lb => retainedMatches 0 | .instr_lh => retainedMatches 1
    | .instr_lw => retainedMatches 2 | .instr_lbu => retainedMatches 3
    | .instr_lhu => retainedMatches 4
    | .instr_sb => retainedMatches 5 | .instr_sh => retainedMatches 6
    | .instr_sw => retainedMatches 7
    | .instr_addi => resetMatches 6 | .instr_slti => resetMatches 7
    | .instr_sltiu => resetMatches 8 | .instr_xori => resetMatches 9
    | .instr_ori => resetMatches 10 | .instr_andi => resetMatches 11
    | .instr_slli => retainedMatches 8 | .instr_srli => retainedMatches 9
    | .instr_srai => retainedMatches 10
    | .instr_add => resetMatches 12 | .instr_sub => resetMatches 13
    | .instr_sll => resetMatches 14 | .instr_slt => resetMatches 15
    | .instr_sltu => resetMatches 16 | .instr_xor => resetMatches 17
    | .instr_srl => resetMatches 18 | .instr_sra => resetMatches 19
    | .instr_or => resetMatches 20 | .instr_and => resetMatches 21
    | .instr_ecall_ebreak => retainedMatches 11
    | .instr_fence => resetMatches 22
    | .is_slli_srli_srai | .is_jalr_addi_slti_sltiu_xori_ori_andi
    | .is_sll_srl_sra => false

private theorem summaryInputs_storageState (inputs : Inputs)
    (resetMatches : Fin 23 → Bool) (retainedMatches : Fin 15 → Bool)
    (immediate : Word) (ordinarySummaries : Fin 4 → Bool)
    (addSubSummary compare : Bool) :
    summaryInputs inputs (storageState resetMatches retainedMatches immediate
      ordinarySummaries addSubSummary compare) =
      summaryInputsOf inputs resetMatches retainedMatches := by
  cases inputs
  congr 1

/-- Group correspondence for the summary layer: registered summaries are
recomputed from the grouped match storage every cycle. -/
private theorem summarized_storageState (inputs : Inputs)
    (resetMatches : Fin 23 → Bool) (retainedMatches : Fin 15 → Bool)
    (immediate : Word) (ordinarySummaries : Fin 4 → Bool)
    (addSubSummary compare : Bool) :
    summarized inputs (storageState resetMatches retainedMatches immediate
      ordinarySummaries addSubSummary compare) =
      storageState resetMatches retainedMatches immediate
        (fun index => instructionSummaryBit
          (summaryInputsOf inputs resetMatches retainedMatches)
          (summaryOutput (ordinarySummaryRegister index)))
        (InstructionSummary.outputValues
          (summaryInputsOf inputs resetMatches retainedMatches)
          .is_lui_auipc_jal_jalr_addi_add_sub)
        (InstructionSummary.outputValues
          (summaryInputsOf inputs resetMatches retainedMatches) .is_compare) := by
  funext register
  cases register <;> rfl

/-- Without a decoder trigger the decode layer is the identity. -/
private theorem decoded_of_untriggered (inputs : Inputs)
    (current updated : stateMap.Values)
    (untriggered : (inputs.decoder_trigger && !inputs.decoder_pseudo_trigger) = false) :
    decoded inputs current updated = updated := by
  unfold decoded
  rw [untriggered]
  rfl

/-- Under reset the reset layer is the identity. -/
private theorem resetApplied_of_resetn (state : stateMap.Values) :
    resetApplied true state = state := rfl

/-- Group correspondence for the decode layer: a trigger replaces both match
groups and the immediate, and clears the two gated summaries. -/
private theorem decoded_storageState (inputs : Inputs)
    (resetMatches : Fin 23 → Bool) (retainedMatches : Fin 15 → Bool)
    (immediate : Word) (ordinarySummaries : Fin 4 → Bool)
    (addSubSummary compare : Bool)
    (updatedResetMatches : Fin 23 → Bool) (updatedRetainedMatches : Fin 15 → Bool)
    (updatedImmediate : Word) (updatedOrdinarySummaries : Fin 4 → Bool)
    (updatedAddSubSummary updatedCompare : Bool) :
    decoded inputs
        (storageState resetMatches retainedMatches immediate ordinarySummaries
          addSubSummary compare)
        (storageState updatedResetMatches updatedRetainedMatches updatedImmediate
          updatedOrdinarySummaries updatedAddSubSummary updatedCompare) =
      storageState
        (bif (inputs.decoder_trigger && !inputs.decoder_pseudo_trigger)
          then fun index => instructionMatchBit (matchInputs inputs)
            (matchOutput (resetMatchRegister index))
          else updatedResetMatches)
        (bif (inputs.decoder_trigger && !inputs.decoder_pseudo_trigger)
          then fun index => instructionMatchBit (matchInputs inputs)
            (matchOutput (retainedMatchRegister index))
          else updatedRetainedMatches)
        (bif (inputs.decoder_trigger && !inputs.decoder_pseudo_trigger)
          then (Immediate.evaluate (immediateInputs inputs)).getD immediate
          else updatedImmediate)
        updatedOrdinarySummaries
        (bif (inputs.decoder_trigger && !inputs.decoder_pseudo_trigger)
          then false else updatedAddSubSummary)
        (bif (inputs.decoder_trigger && !inputs.decoder_pseudo_trigger)
          then false else updatedCompare) := by
  cases trigger : (inputs.decoder_trigger && !inputs.decoder_pseudo_trigger)
  · rw [decoded_of_untriggered inputs _ _ trigger]
    rfl
  · unfold decoded
    rw [if_neg (by simp [trigger])]
    funext register
    cases register <;> rfl

/-- Group correspondence for the reset layer: reset clears exactly the
reset-match group and the compare summary. -/
private theorem resetApplied_storageState (resetn : Bool)
    (resetMatches : Fin 23 → Bool) (retainedMatches : Fin 15 → Bool)
    (immediate : Word) (ordinarySummaries : Fin 4 → Bool)
    (addSubSummary compare : Bool) :
    resetApplied resetn (storageState resetMatches retainedMatches immediate
      ordinarySummaries addSubSummary compare) =
      storageState (bif !resetn then falseResetMatches else resetMatches)
        retainedMatches immediate ordinarySummaries addSubSummary
        (bif !resetn then false else compare) := by
  cases resetn
  · funext register
    simp only [resetApplied, Bool.not_false, cond_true]
    cases register <;> rfl
  · rw [resetApplied_of_resetn]
    rfl

/-- The contract's next state, read through the structural grouping. -/
private theorem nextState_grouped (inputs : Inputs)
    (resetMatches : Fin 23 → Bool) (retainedMatches : Fin 15 → Bool)
    (immediate : Word) (ordinarySummaries : Fin 4 → Bool)
    (addSubSummary compare : Bool) :
    nextState inputs (storageState resetMatches retainedMatches immediate
      ordinarySummaries addSubSummary compare) =
      storageState
        (bif !inputs.resetn then falseResetMatches
          else bif (inputs.decoder_trigger && !inputs.decoder_pseudo_trigger)
            then fun index => instructionMatchBit (matchInputs inputs)
              (matchOutput (resetMatchRegister index))
            else resetMatches)
        (bif (inputs.decoder_trigger && !inputs.decoder_pseudo_trigger)
          then fun index => instructionMatchBit (matchInputs inputs)
            (matchOutput (retainedMatchRegister index))
          else retainedMatches)
        (bif (inputs.decoder_trigger && !inputs.decoder_pseudo_trigger)
          then (Immediate.evaluate (immediateInputs inputs)).getD immediate
          else immediate)
        (fun index => instructionSummaryBit
          (summaryInputsOf inputs resetMatches retainedMatches)
          (summaryOutput (ordinarySummaryRegister index)))
        (bif (inputs.decoder_trigger && !inputs.decoder_pseudo_trigger)
          then false else InstructionSummary.outputValues
            (summaryInputsOf inputs resetMatches retainedMatches)
            .is_lui_auipc_jal_jalr_addi_add_sub)
        (bif !inputs.resetn then false
          else bif (inputs.decoder_trigger && !inputs.decoder_pseudo_trigger)
            then false else InstructionSummary.outputValues
              (summaryInputsOf inputs resetMatches retainedMatches) .is_compare) := by
  rw [nextState, summarized_storageState, decoded_storageState,
    resetApplied_storageState]

/-- The registered immediate keeps its previous value exactly when the
combinational immediate is invalid. -/
private theorem immediateSelection_getD (inputs : Immediate.Inputs)
    (retained : Word) :
    (bif Immediate.outputValues inputs .valid then
        Immediate.outputValues inputs .value else retained) =
      (Immediate.evaluate inputs).getD retained := by
  cases evaluation : Immediate.evaluate inputs <;>
    simp [Immediate.outputValues, evaluation]

/-- Semantic correspondence for the instruction-summary child's inputs: the
split match groups feed it exactly the contract's registered match values. -/
private theorem summaryValues_of_childOutputs
    (inputs : inputMap.Values)
    (childOutputs : (child : Instance) → (instancePorts.ports child).outputs.Values)
    (resetMatches : Fin 23 → Bool) (retainedMatches : Fin 15 → Bool)
    (resetValues : ∀ index, childOutputs .resetMatchOutputs index = resetMatches index)
    (retainedValues : ∀ index,
      childOutputs .retainedMatchOutputs index = retainedMatches index) :
    InstructionSummary.valuesOf (instructionSummaryInputs inputs childOutputs) =
      summaryInputsOf (valuesOf inputs) resetMatches retainedMatches := by
  unfold InstructionSummary.valuesOf
  congr 1
  funext output
  cases output <;> first
    | exact resetValues _
    | exact retainedValues _
    | rfl

/-- The child's illegal-instruction view agrees with the contract's. -/
private theorem recognized_storageState (inputs : Inputs)
    (resetMatches : Fin 23 → Bool) (retainedMatches : Fin 15 → Bool)
    (immediate : Word) (ordinarySummaries : Fin 4 → Bool)
    (addSubSummary compare : Bool) :
    InstructionSummary.recognized
        (summaryInputsOf inputs resetMatches retainedMatches) =
      recognized inputs (storageState resetMatches retainedMatches immediate
        ordinarySummaries addSubSummary compare) := rfl

section LayerCertification

variable (layerChildren : ChildStructures body childContracts)

private def stateCorresponds (contractState : stateMap.Values)
    (structuralState : (Contracts.Cycle.Certification.Layer.moduleStructure
      body layerChildren).State) : Prop :=
  ∃ (resetMatches : Fin 23 → Bool) (retainedMatches : Fin 15 → Bool)
      (immediate : Word) (ordinarySummaries : Fin 4 → Bool)
      (addSubSummary compare : Bool),
    (layerChildren .resetMatchStorage).certification.stateCorresponds
        (fun | .stored => resetMatches) (structuralState .resetMatchStorage) ∧
    (layerChildren .retainedMatchStorage).certification.stateCorresponds
        (fun | .stored => retainedMatches) (structuralState .retainedMatchStorage) ∧
    (layerChildren .immediateStorage).certification.stateCorresponds
        (fun | .stored => immediate) (structuralState .immediateStorage) ∧
    (layerChildren .ordinarySummaryStorage).certification.stateCorresponds
        (fun | .stored => ordinarySummaries) (structuralState .ordinarySummaryStorage) ∧
    (layerChildren .addSubSummaryStorage).certification.stateCorresponds
        (fun | .stored => addSubSummary) (structuralState .addSubSummaryStorage) ∧
    (layerChildren .compareStorage).certification.stateCorresponds
        (fun | .stored => compare) (structuralState .compareStorage) ∧
    contractState = storageState resetMatches retainedMatches immediate
      ordinarySummaries addSubSummary compare

private theorem hasCorrespondingState
    (structuralState : (Contracts.Cycle.Certification.Layer.moduleStructure
      body layerChildren).State) :
    ∃ contractState, stateCorresponds layerChildren contractState structuralState := by
  rcases (layerChildren .resetMatchStorage).certification.hasCorrespondingState
      (structuralState .resetMatchStorage) with ⟨resetState, resetCorresponds⟩
  rcases (layerChildren .retainedMatchStorage).certification.hasCorrespondingState
      (structuralState .retainedMatchStorage) with ⟨retainedState, retainedCorresponds⟩
  rcases (layerChildren .immediateStorage).certification.hasCorrespondingState
      (structuralState .immediateStorage) with ⟨immediateState, immediateCorresponds⟩
  rcases (layerChildren .ordinarySummaryStorage).certification.hasCorrespondingState
      (structuralState .ordinarySummaryStorage) with ⟨ordinaryState, ordinaryCorresponds⟩
  rcases (layerChildren .addSubSummaryStorage).certification.hasCorrespondingState
      (structuralState .addSubSummaryStorage) with ⟨addSubState, addSubCorresponds⟩
  rcases (layerChildren .compareStorage).certification.hasCorrespondingState
      (structuralState .compareStorage) with ⟨compareState, compareCorresponds⟩
  refine ⟨storageState (resetState .stored) (retainedState .stored)
    (immediateState .stored) (ordinaryState .stored) (addSubState .stored)
    (compareState .stored), ?_⟩
  exact ⟨resetState .stored, retainedState .stored, immediateState .stored,
    ordinaryState .stored, addSubState .stored, compareState .stored,
    resetCorresponds, retainedCorresponds, immediateCorresponds,
    ordinaryCorresponds, addSubCorresponds, compareCorresponds, rfl⟩

private theorem implements :
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  rcases corresponds with ⟨resetMatches, retainedMatches, immediate,
    ordinarySummaries, addSubSummary, compare, resetCorresponds,
    retainedCorresponds, immediateCorresponds, ordinaryCorresponds,
    addSubCorresponds, compareCorresponds, stateEqual⟩
  subst contractState
  have resetMatch := childSolutionMatchesContract layerChildren hierStep
    satisfies .resetMatchStorage
    (fun | .stored => resetMatches) resetCorresponds
  have retainedMatch := childSolutionMatchesContract layerChildren hierStep
    satisfies .retainedMatchStorage
    (fun | .stored => retainedMatches) retainedCorresponds
  have immediateMatch := childSolutionMatchesContract layerChildren hierStep
    satisfies .immediateStorage
    (fun | .stored => immediate) immediateCorresponds
  have ordinaryMatch := childSolutionMatchesContract layerChildren hierStep
    satisfies .ordinarySummaryStorage
    (fun | .stored => ordinarySummaries) ordinaryCorresponds
  have addSubMatch := childSolutionMatchesContract layerChildren hierStep
    satisfies .addSubSummaryStorage
    (fun | .stored => addSubSummary) addSubCorresponds
  have compareMatch := childSolutionMatchesContract layerChildren hierStep
    satisfies .compareStorage
    (fun | .stored => compare) compareCorresponds
  have coveredMatch (child : Instance) :=
    (childSolutionMatchesCoveredContract layerChildren hierStep satisfies child).choose_spec
  have summaryMatch := coveredMatch .instructionSummary

  have resetCurrent : hierStep.childOutputs .resetMatchStorage .value = resetMatches :=
    (Modules.EnabledResetRegister.observeRule_holds_iff
      resetMatchType falseResetMatches _ _ _).mp
        (resetMatch.ruleHolds Modules.EnabledResetRegister.Rule.observe)
  have retainedCurrent : hierStep.childOutputs .retainedMatchStorage .q = retainedMatches :=
    (Modules.EnabledRegister.observeRule_holds_iff retainedMatchType _ _ _).mp
      (retainedMatch.ruleHolds Modules.EnabledRegister.Rule.observe)
  have immediateCurrent : hierStep.childOutputs .immediateStorage .q = immediate :=
    (Modules.EnabledRegister.observeRule_holds_iff immediateType _ _ _).mp
      (immediateMatch.ruleHolds Modules.EnabledRegister.Rule.observe)
  have ordinaryCurrent : hierStep.childOutputs .ordinarySummaryStorage .output =
      ordinarySummaries :=
    (Modules.Register.outputRule_holds_iff ordinarySummaryType _ _ _).mp
      (ordinaryMatch.ruleHolds Primitives.RegisterRule.observe)
  have addSubCurrent : hierStep.childOutputs .addSubSummaryStorage .output =
      addSubSummary :=
    (Modules.Register.outputRule_holds_iff .bit _ _ _).mp
      (addSubMatch.ruleHolds Primitives.RegisterRule.observe)
  have compareCurrent : hierStep.childOutputs .compareStorage .value = compare :=
    (Modules.ResetRegister.observeRule_holds_iff .bit false _ _ _).mp
      (compareMatch.ruleHolds Modules.ResetRegister.Rule.observe)

  have resetOutputsEquation :=
    (Composition.SignalSplitter.outputRule_holds_iff resetMatchSplitter _ _ _).mp
      ((coveredMatch .resetMatchOutputs).ruleHolds Composition.SignalComponentRule.apply)
  have retainedOutputsEquation :=
    (Composition.SignalSplitter.outputRule_holds_iff retainedMatchSplitter _ _ _).mp
      ((coveredMatch .retainedMatchOutputs).ruleHolds Composition.SignalComponentRule.apply)
  have ordinaryOutputsEquation :=
    (Composition.SignalSplitter.outputRule_holds_iff ordinarySummarySplitter _ _ _).mp
      ((coveredMatch .ordinarySummaryOutputs).ruleHolds Composition.SignalComponentRule.apply)
  dsimp only at resetOutputsEquation retainedOutputsEquation ordinaryOutputsEquation
  have resetOutputValue (index : Fin 23) :
      hierStep.childOutputs .resetMatchOutputs index = resetMatches index := by
    have equation := congrFun resetOutputsEquation index
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrFun resetCurrent index)
  have retainedOutputValue (index : Fin 15) :
      hierStep.childOutputs .retainedMatchOutputs index = retainedMatches index := by
    have equation := congrFun retainedOutputsEquation index
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrFun retainedCurrent index)
  have ordinaryOutputValue (index : Fin 4) :
      hierStep.childOutputs .ordinarySummaryOutputs index = ordinarySummaries index := by
    have equation := congrFun ordinaryOutputsEquation index
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (congrFun ordinaryCurrent index)
  have summaryValues : InstructionSummary.valuesOf
      (instructionSummaryInputs hierStep.inputs (fun child => hierStep.childOutputs child)) =
      summaryInputsOf (valuesOf hierStep.inputs) resetMatches retainedMatches :=
    summaryValues_of_childOutputs hierStep.inputs _ resetMatches retainedMatches
      resetOutputValue retainedOutputValue

  let matchValues : InstructionMatch.Inputs := matchInputs (valuesOf hierStep.inputs)
  have instructionOutputs : hierStep.childOutputs .instructionMatch =
      InstructionMatch.outputValues matchValues := by
    have equation := (InstructionMatch.outputRule_holds_iff _ _ _).mp
      ((coveredMatch .instructionMatch).ruleHolds InstructionMatch.Rule.apply)
    simpa [matchValues, matchInputs, valuesOf,
      body, wiring, context, EndpointContext.moduleInput, SignalSource.value,
      InstructionMatch.valuesOf] using equation

  let immediateValues : Immediate.Inputs := immediateInputs (valuesOf hierStep.inputs)
  have immediateOutputs : hierStep.childOutputs .immediate =
      Immediate.outputValues immediateValues := by
    have equation := (Immediate.outputRule_holds_iff _ _ _).mp
      ((coveredMatch .immediate).ruleHolds Immediate.Rule.apply)
    simpa [immediateValues, immediateInputs, valuesOf,
      body, wiring, context,
      EndpointContext.moduleInput, SignalSource.value,
      Immediate.valuesOf] using equation

  have summaryInputsEqual :
      body.wiring.childInputValues hierStep.inputs hierStep.childOutputs
          .instructionSummary =
        instructionSummaryInputs hierStep.inputs (fun child => hierStep.childOutputs child) := by
    funext input
    exact instructionSummaryInput_value hierStep.inputs
      (fun child => hierStep.childOutputs child) input
  have summaryOutputValue (output : InstructionSummary.Output)
      (notTrap : output ≠ .instr_trap) :
      hierStep.childOutputs .instructionSummary output =
        InstructionSummary.outputValues
          (InstructionSummary.valuesOf (instructionSummaryInputs hierStep.inputs
            (fun child => hierStep.childOutputs child))) output := by
    have held := (InstructionSummary.summariesOutputRule_holds_iff _ _ _).mp
      (summaryMatch.ruleHolds InstructionSummary.Rule.summaries)
    rw [summaryInputsEqual] at held
    exact held output notTrap

  have pseudoValue : hierStep.childOutputs .pseudoInverter .output =
      !(hierStep.inputs .decoder_pseudo_trigger) := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((coveredMatch .pseudoInverter).ruleHolds Primitives.NotRule.apply)
    simpa [body, wiring, context,
      EndpointContext.moduleInput, SignalSource.value] using equation
  have triggerValue : hierStep.childOutputs .triggerEnable .output =
      (hierStep.inputs .decoder_trigger && !(hierStep.inputs .decoder_pseudo_trigger)) := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      ((coveredMatch .triggerEnable).ruleHolds Primitives.AndRule.apply)
    normalize_child_hyp equation unfolding wiring, context
    exact equation.trans (apply₂_congr Bool.and rfl pseudoValue)
  have resetValue : hierStep.childOutputs .resetInverter .output =
      !(hierStep.inputs .resetn) := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((coveredMatch .resetInverter).ruleHolds Primitives.NotRule.apply)
    simpa [body, wiring, context,
      EndpointContext.moduleInput, SignalSource.value] using equation
  have falseValue : hierStep.childOutputs .falseValue .output = false := by
    exact Modules.Constant.output_of_allowed .bit false
      (coveredMatch .falseValue).allowed

  have resetNextValue : hierStep.childOutputs .resetMatchNext .value =
      fun index => instructionMatchBit matchValues
        (matchOutput (resetMatchRegister index)) := by
    have equation := (Composition.SignalCombiner.outputRule_holds_iff
      resetMatchCombiner _ _ _).mp
        ((coveredMatch .resetMatchNext).ruleHolds Composition.SignalComponentRule.apply)
    dsimp only at equation
    have valueEquation := congrFun equation .value
    rw [valueEquation]
    funext index
    change (SignalSource.castType (InstructionMatch.output_signalType _)
      (context.instanceOutput .instructionMatch
        (matchOutput (resetMatchRegister index)))).value hierStep.inputs
          (fun child => hierStep.childOutputs child) = _
    rw [SignalSource.value_castType]
    simp only [EndpointContext.instanceOutput, SignalSource.value]
    rw [signalType_subst_eq_mp]
    unfold instructionMatchBit
    exact congrArg (fun values =>
      Eq.mp (congrArg SignalType.Denote (InstructionMatch.output_signalType
        (matchOutput (resetMatchRegister index))))
        (values (matchOutput (resetMatchRegister index)))) instructionOutputs
  have retainedNextValue : hierStep.childOutputs .retainedMatchNext .value =
      fun index => instructionMatchBit matchValues
        (matchOutput (retainedMatchRegister index)) := by
    have equation := (Composition.SignalCombiner.outputRule_holds_iff
      retainedMatchCombiner _ _ _).mp
        ((coveredMatch .retainedMatchNext).ruleHolds Composition.SignalComponentRule.apply)
    dsimp only at equation
    have valueEquation := congrFun equation .value
    rw [valueEquation]
    funext index
    change (SignalSource.castType (InstructionMatch.output_signalType _)
      (context.instanceOutput .instructionMatch
        (matchOutput (retainedMatchRegister index)))).value hierStep.inputs
          (fun child => hierStep.childOutputs child) = _
    rw [SignalSource.value_castType]
    simp only [EndpointContext.instanceOutput, SignalSource.value]
    rw [signalType_subst_eq_mp]
    unfold instructionMatchBit
    exact congrArg (fun values =>
      Eq.mp (congrArg SignalType.Denote (InstructionMatch.output_signalType
        (matchOutput (retainedMatchRegister index))))
        (values (matchOutput (retainedMatchRegister index)))) instructionOutputs
  have ordinaryNextEquation :=
    (Composition.SignalCombiner.outputRule_holds_iff
      ordinarySummaryCombiner _ _ _).mp
        ((coveredMatch .ordinarySummaryNext).ruleHolds Composition.SignalComponentRule.apply)
  dsimp only at ordinaryNextEquation
  have ordinaryNotTrap (index : Fin 4) :
      summaryOutput (ordinarySummaryRegister index) ≠
        InstructionSummary.Output.instr_trap := by
    refine Fin.cases ?_ (fun index => ?_) index
    · intro equal; cases equal
    · refine Fin.cases ?_ (fun index => ?_) index
      · intro equal; cases equal
      · refine Fin.cases ?_ (fun index => ?_) index
        · intro equal; cases equal
        · refine Fin.cases ?_ (fun index => ?_) index
          · intro equal; cases equal
          · exact Fin.elim0 index
  have ordinaryNextValue : hierStep.childOutputs .ordinarySummaryNext .value =
      fun index => instructionSummaryBit
        (summaryInputsOf (valuesOf hierStep.inputs) resetMatches retainedMatches)
        (summaryOutput (ordinarySummaryRegister index)) := by
    rw [← summaryValues, congrFun ordinaryNextEquation .value]
    funext index
    change (SignalSource.castType (InstructionSummary.output_signalType _)
      (context.instanceOutput .instructionSummary
        (summaryOutput (ordinarySummaryRegister index)))).value hierStep.inputs
          (fun child => hierStep.childOutputs child) = _
    rw [SignalSource.value_castType]
    simp only [EndpointContext.instanceOutput, SignalSource.value]
    rw [signalType_subst_eq_mp]
    unfold instructionSummaryBit
    exact congrArg (fun value =>
      Eq.mp (congrArg SignalType.Denote (InstructionSummary.output_signalType
        (summaryOutput (ordinarySummaryRegister index)))) value)
      (summaryOutputValue _ (ordinaryNotTrap index))

  have immediateSelectionEquation := Modules.Mux.result_of_allowed
    immediateType (coveredMatch .immediateSelection).allowed
  normalize_child_hyp immediateSelectionEquation unfolding wiring, context
  have immediateSelectionValue := immediateSelectionEquation.trans
    (bif_congr (congrFun immediateOutputs .valid)
      (congrFun immediateOutputs .value) immediateCurrent)

  have addSubSummaryValue :=
    summaryOutputValue .is_lui_auipc_jal_jalr_addi_add_sub
      (by intro equal; cases equal)
  rw [summaryValues] at addSubSummaryValue
  have addSubSelectionEquation := Modules.Mux.result_of_allowed
    .bit (coveredMatch .addSubSummarySelection).allowed
  normalize_child_hyp addSubSelectionEquation unfolding wiring, context
  have addSubSelectionValue := addSubSelectionEquation.trans
    (bif_congr triggerValue falseValue addSubSummaryValue)

  have compareSummaryValue := summaryOutputValue .is_compare
    (by intro equal; cases equal)
  rw [summaryValues] at compareSummaryValue
  have compareSelectionEquation := Modules.Mux.result_of_allowed
    .bit (coveredMatch .compareSelection).allowed
  normalize_child_hyp compareSelectionEquation unfolding wiring, context
  have compareSelectionValue := compareSelectionEquation.trans
    (bif_congr triggerValue falseValue compareSummaryValue)

  have trapValue : hierStep.childOutputs .instructionSummary .instr_trap =
      outputValues (valuesOf hierStep.inputs)
        (storageState resetMatches retainedMatches immediate ordinarySummaries
          addSubSummary compare) .instr_trap := by
    have equation := (InstructionSummary.trapOutputRule_holds_iff _ _ _).mp
      (summaryMatch.ruleHolds InstructionSummary.Rule.trap)
    rw [summaryInputsEqual] at equation
    change hierStep.childOutputs .instructionSummary .instr_trap =
      !(InstructionSummary.recognized (InstructionSummary.valuesOf
        (instructionSummaryInputs hierStep.inputs
          (fun child => hierStep.childOutputs child)))) at equation
    rw [equation, summaryValues, recognized_storageState (valuesOf hierStep.inputs)
      resetMatches retainedMatches immediate ordinarySummaries addSubSummary
      compare]
    rfl

  have boundaryEqual : hierStep.outputs =
      boundaryValues (fun child => hierStep.childOutputs child) := by
    funext output
    exact (satisfies.1 output).trans
      (moduleOutput_value hierStep.inputs (fun child => hierStep.childOutputs child) output)

  let next := nextState (valuesOf hierStep.inputs)
    (storageState resetMatches retainedMatches immediate ordinarySummaries
      addSubSummary compare)
  refine ⟨next, ?_, ?_⟩
  · constructor
    · intro rule
      cases rule
      rw [outputRule_holds_iff]
      change hierStep.outputs = outputValues (valuesOf hierStep.inputs)
        (storageState resetMatches retainedMatches immediate ordinarySummaries
          addSubSummary compare)
      rw [boundaryEqual]
      funext output
      cases output <;>
        simp only [boundaryValues, outputValues, storageState] <;>
        first
        | exact trapValue
        | exact resetOutputValue _
        | exact retainedOutputValue _
        | exact immediateCurrent
        | exact ordinaryOutputValue _
        | exact addSubCurrent
        | exact compareCurrent
    · rfl
  · let resetNextState := (childContracts .resetMatchStorage).stateRule.apply
      (body.wiring.childInputValues hierStep.inputs hierStep.childOutputs
        .resetMatchStorage) (fun | .stored => resetMatches)
    let retainedNextState := (childContracts .retainedMatchStorage).stateRule.apply
      (body.wiring.childInputValues hierStep.inputs hierStep.childOutputs
        .retainedMatchStorage) (fun | .stored => retainedMatches)
    let immediateNextState := (childContracts .immediateStorage).stateRule.apply
      (body.wiring.childInputValues hierStep.inputs hierStep.childOutputs
        .immediateStorage) (fun | .stored => immediate)
    let ordinaryNextState :=
      (childContracts .ordinarySummaryStorage).stateRule.apply
        (body.wiring.childInputValues hierStep.inputs hierStep.childOutputs
          .ordinarySummaryStorage) (fun | .stored => ordinarySummaries)
    let addSubNextState := (childContracts .addSubSummaryStorage).stateRule.apply
      (body.wiring.childInputValues hierStep.inputs hierStep.childOutputs
        .addSubSummaryStorage) (fun | .stored => addSubSummary)
    let compareNextState := (childContracts .compareStorage).stateRule.apply
      (body.wiring.childInputValues hierStep.inputs hierStep.childOutputs
        .compareStorage) (fun | .stored => compare)
    have resetNextStored : resetNextState .stored =
        bif !(hierStep.inputs .resetn) then falseResetMatches
        else bif (hierStep.inputs .decoder_trigger && !(hierStep.inputs .decoder_pseudo_trigger))
          then (fun index => instructionMatchBit matchValues
            (matchOutput (resetMatchRegister index)))
          else resetMatches := by
      change (bif hierStep.childOutputs .resetInverter .output
        then falseResetMatches
        else bif hierStep.childOutputs .triggerEnable .output
          then hierStep.childOutputs .resetMatchNext .value
          else resetMatches) = _
      rw [resetValue, triggerValue]
      cases hierStep.inputs .resetn <;>
        cases hierStep.inputs .decoder_trigger && !(hierStep.inputs .decoder_pseudo_trigger) <;>
        simp [resetNextValue]
    have retainedNextStored : retainedNextState .stored =
        bif (hierStep.inputs .decoder_trigger && !(hierStep.inputs .decoder_pseudo_trigger))
          then (fun index => instructionMatchBit matchValues
            (matchOutput (retainedMatchRegister index)))
          else retainedMatches := by
      change (bif hierStep.childOutputs .triggerEnable .output
        then hierStep.childOutputs .retainedMatchNext .value
        else retainedMatches) = _
      rw [triggerValue]
      cases hierStep.inputs .decoder_trigger && !(hierStep.inputs .decoder_pseudo_trigger) <;>
        simp [retainedNextValue]
    have immediateNextStored : immediateNextState .stored =
        bif (hierStep.inputs .decoder_trigger && !(hierStep.inputs .decoder_pseudo_trigger))
          then (Immediate.evaluate immediateValues).getD immediate
          else immediate := by
      change (bif hierStep.childOutputs .triggerEnable .output
        then hierStep.childOutputs .immediateSelection .result
        else immediate) = _
      exact bif_congr triggerValue
        (immediateSelectionValue.trans
          (immediateSelection_getD immediateValues immediate)) rfl
    have ordinaryNextStored : ordinaryNextState .stored =
        fun index => instructionSummaryBit
          (summaryInputsOf (valuesOf hierStep.inputs) resetMatches retainedMatches)
          (summaryOutput (ordinarySummaryRegister index)) := by
      change hierStep.childOutputs .ordinarySummaryNext .value = _
      exact ordinaryNextValue
    have addSubNextStored : addSubNextState .stored =
        bif (hierStep.inputs .decoder_trigger && !(hierStep.inputs .decoder_pseudo_trigger))
          then false
          else InstructionSummary.outputValues
            (summaryInputsOf (valuesOf hierStep.inputs) resetMatches retainedMatches)
            .is_lui_auipc_jal_jalr_addi_add_sub := by
      change hierStep.childOutputs .addSubSummarySelection .result = _
      exact addSubSelectionValue
    have compareNextStored : compareNextState .stored =
        bif !(hierStep.inputs .resetn) then false
        else bif (hierStep.inputs .decoder_trigger && !(hierStep.inputs .decoder_pseudo_trigger))
          then false
          else InstructionSummary.outputValues
            (summaryInputsOf (valuesOf hierStep.inputs) resetMatches retainedMatches)
            .is_compare := by
      change (bif hierStep.childOutputs .resetInverter .output then false
        else hierStep.childOutputs .compareSelection .result) = _
      exact bif_congr resetValue rfl compareSelectionValue
    refine ⟨resetNextState .stored, retainedNextState .stored,
      immediateNextState .stored, ordinaryNextState .stored,
      addSubNextState .stored, compareNextState .stored, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact resetMatch.2
    · exact retainedMatch.2
    · exact immediateMatch.2
    · exact ordinaryMatch.2
    · exact addSubMatch.2
    · exact compareMatch.2
    · rw [resetNextStored, retainedNextStored, immediateNextStored,
        ordinaryNextStored, addSubNextStored, compareNextStored]
      exact nextState_grouped (valuesOf hierStep.inputs) resetMatches retainedMatches
        immediate ordinarySummaries addSubSummary compare

end LayerCertification

module_cycle_certification certification for moduleStructure via body
    with childContracts implementing cycleContract where
  schedules := derivedRuleSchedules,
  structuralChildren := structuralChildren,
  certifiedChildren := certifiedChildren,
  structuresMatch := certifiedChildren_moduleStructure,
  stateCorresponds := stateCorresponds,
  stateCoverage := hasCorrespondingState,
  implements := implements

end Silean.Examples.PicoRV.Decoder.ResolveStage
