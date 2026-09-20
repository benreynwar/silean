import PicoRV.Regs
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Mux.MuxTheorems
import Silean.Modules.RegisterBank.RegisterBankTheorems
import Silean.Modules.Equality.EqualityTheorems

/-! # PicoRV register-file verification

Child certifications, schedules, structural state correspondence, and the
native `HierStep` implementation proof live here. Downstream proofs should
import `RegsTheorems`.
-/

namespace PicoRV.Regs

open Silean
open Silean.Authoring
open Silean.Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  bank := Silean.Modules.RegisterBank.certification wordType 5 2,
  zeroAddress := Silean.Modules.Constant.certification addressType zeroAddressValue,
  zeroWord := Silean.Modules.Constant.certification wordType zeroWordValue,
  rs1Zero := Silean.Modules.Equality.certification addressType,
  rs2Zero := Silean.Modules.Equality.certification addressType,
  rdZero := Silean.Modules.Equality.certification addressType,
  rdNonzero := Silean.Primitives.notCertified.certification,
  requestedWrite := Silean.Primitives.andCertified.certification,
  enabledWrite := Silean.Primitives.andCertified.certification,
  rs1Mux := Silean.Modules.Mux.certification wordType,
  rs2Mux := Silean.Modules.Mux.certification wordType

/-! ## Cycle certification -/

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .cpuregs_rs1 => [.zeroAddress => Silean.Primitives.ConstantRule.apply,
        .zeroWord => Silean.Primitives.ConstantRule.apply,
        .rs1Zero => Silean.Modules.Equality.Rule.apply,
        .bank => Silean.Modules.RegisterBank.Rule.read 0,
        .rs1Mux => Silean.Modules.Mux.Rule.select]
    | .cpuregs_rs2 => [.zeroAddress => Silean.Primitives.ConstantRule.apply,
        .zeroWord => Silean.Primitives.ConstantRule.apply,
        .rs2Zero => Silean.Modules.Equality.Rule.apply,
        .bank => Silean.Modules.RegisterBank.Rule.read 1,
        .rs2Mux => Silean.Modules.Mux.Rule.select]
  state := [.zeroAddress => Silean.Primitives.ConstantRule.apply,
    .rdZero => Silean.Modules.Equality.Rule.apply,
    .rdNonzero => Silean.Primitives.NotRule.apply,
    .requestedWrite => Silean.Primitives.AndRule.apply,
    .enabledWrite => Silean.Primitives.AndRule.apply]

section LayerCertification

variable (layerChildren : Silean.Contracts.Cycle.Certification.Layer.ChildStructures
  body childContracts)

private def stateCorresponds (contractState : cycleContract.state.Values)
    (structuralState :
      (Silean.Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren).State) : Prop :=
  (layerChildren .bank).certification.stateCorresponds
    (fun | .entries => contractState .cpuregs) (structuralState .bank)

private theorem hasCorrespondingState
    (structuralState :
      (Silean.Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren).State) :
    ∃ contractState, stateCorresponds layerChildren contractState structuralState := by
  rcases (layerChildren .bank).certification.hasCorrespondingState
      (structuralState .bank) with
    ⟨bankState, bankCorresponds⟩
  exact ⟨fun | .cpuregs => bankState .entries, bankCorresponds⟩

private theorem implements :
    Silean.Contracts.Cycle.ImplementsSolutions
      (Silean.Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_match zeroAddressMatch for .zeroAddress
    in body from layerChildren, hierStep, satisfies
  derive_empty_state_child_match zeroWordMatch for .zeroWord
    in body from layerChildren, hierStep, satisfies
  derive_empty_state_child_match rs1ZeroMatch for .rs1Zero
    in body from layerChildren, hierStep, satisfies
  derive_empty_state_child_match rs2ZeroMatch for .rs2Zero
    in body from layerChildren, hierStep, satisfies
  derive_empty_state_child_match rdZeroMatch for .rdZero
    in body from layerChildren, hierStep, satisfies
  derive_empty_state_child_match rdNonzeroMatch for .rdNonzero
    in body from layerChildren, hierStep, satisfies
  derive_empty_state_child_match requestedWriteMatch for .requestedWrite
    in body from layerChildren, hierStep, satisfies
  derive_empty_state_child_match enabledWriteMatch for .enabledWrite
    in body from layerChildren, hierStep, satisfies
  derive_empty_state_child_match rs1MuxMatch for .rs1Mux
    in body from layerChildren, hierStep, satisfies
  derive_empty_state_child_match rs2MuxMatch for .rs2Mux
    in body from layerChildren, hierStep, satisfies
  have bankMatches := Silean.Contracts.Cycle.Certification.Layer.childSolutionMatchesContract
    layerChildren hierStep satisfies .bank
    (fun | .entries => contractState .cpuregs) corresponds

  have zeroAddressValueEq : (hierStep.children .zeroAddress).outputs .output = zeroAddressValue :=
    Silean.Modules.Constant.output_of_allowed addressType zeroAddressValue
      zeroAddressMatch.allowed
  have zeroWordValueEq : (hierStep.children .zeroWord).outputs .output = zeroWordValue :=
    Silean.Modules.Constant.output_of_allowed wordType zeroWordValue
      zeroWordMatch.allowed
  have zeroWordsEqual : zeroWordValue = zeroWord := rfl
  have rs1ZeroValue : (hierStep.children .rs1Zero).outputs .result =
      addressType.equal (hierStep.inputs .decoded_rs1) zeroAddressValue := by
    have held := Silean.Modules.Equality.result_of_allowed addressType
      rs1ZeroMatch.allowed
    have wired : (hierStep.children .rs1Zero).outputs .result =
        addressType.equal (hierStep.inputs .decoded_rs1) ((hierStep.children .zeroAddress).outputs .output) := by
      simpa [Silean.HierStep.childOutputs, Silean.Wiring.childInputValues, body, wiring, context, instancePorts,
        Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput, Silean.SignalSource.value] using held
    rw [zeroAddressValueEq] at wired
    exact wired
  have rs2ZeroValue : (hierStep.children .rs2Zero).outputs .result =
      addressType.equal (hierStep.inputs .decoded_rs2) zeroAddressValue := by
    have held := Silean.Modules.Equality.result_of_allowed addressType
      rs2ZeroMatch.allowed
    have wired : (hierStep.children .rs2Zero).outputs .result =
        addressType.equal (hierStep.inputs .decoded_rs2) ((hierStep.children .zeroAddress).outputs .output) := by
      simpa [Silean.HierStep.childOutputs, Silean.Wiring.childInputValues, body, wiring, context, instancePorts,
        Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput, Silean.SignalSource.value] using held
    rw [zeroAddressValueEq] at wired
    exact wired
  have rdZeroValue : (hierStep.children .rdZero).outputs .result =
      addressType.equal (hierStep.inputs .latched_rd) zeroAddressValue := by
    have held := Silean.Modules.Equality.result_of_allowed addressType
      rdZeroMatch.allowed
    have wired : (hierStep.children .rdZero).outputs .result =
        addressType.equal (hierStep.inputs .latched_rd) ((hierStep.children .zeroAddress).outputs .output) := by
      simpa [Silean.HierStep.childOutputs, Silean.Wiring.childInputValues, body, wiring, context, instancePorts,
        Silean.EndpointContext.moduleInput, Silean.EndpointContext.instanceOutput, Silean.SignalSource.value] using held
    rw [zeroAddressValueEq] at wired
    exact wired
  have rdNonzeroValue : (hierStep.children .rdNonzero).outputs .output =
      !addressType.equal (hierStep.inputs .latched_rd) zeroAddressValue := by
    have held := (Silean.Primitives.notOutputRule_holds_iff _ _ _).mp
      (rdNonzeroMatch.ruleHolds Silean.Primitives.NotRule.apply)
    normalize_child_hyp held unfolding wiring, context
    exact held.trans (congrArg Bool.not rdZeroValue)
  have requestedWriteValue : (hierStep.children .requestedWrite).outputs .output =
      (hierStep.inputs .resetn && hierStep.inputs .cpuregs_write) := by
    have held := (Silean.Primitives.andOutputRule_holds_iff _ _ _).mp
      (requestedWriteMatch.ruleHolds Silean.Primitives.AndRule.apply)
    simpa [Silean.HierStep.childOutputs, Silean.Wiring.childInputValues, body, wiring, context, instancePorts,
      Silean.EndpointContext.moduleInput, Silean.SignalSource.value] using held
  have enabledWriteValue : (hierStep.children .enabledWrite).outputs .output =
      ((hierStep.inputs .resetn && hierStep.inputs .cpuregs_write) &&
        !addressType.equal (hierStep.inputs .latched_rd) zeroAddressValue) := by
    have held := (Silean.Primitives.andOutputRule_holds_iff _ _ _).mp
      (enabledWriteMatch.ruleHolds Silean.Primitives.AndRule.apply)
    normalize_child_hyp held unfolding wiring, context
    have pairEqual :
        ((hierStep.children .requestedWrite).outputs .output,
          (hierStep.children .rdNonzero).outputs .output) =
        ((hierStep.inputs .resetn && hierStep.inputs .cpuregs_write),
          !addressType.equal (hierStep.inputs .latched_rd) zeroAddressValue) :=
      Prod.ext requestedWriteValue rdNonzeroValue
    exact held.trans (congrArg (fun pair : Bool × Bool => pair.1 && pair.2)
      pairEqual)

  have bankRead1Value : (hierStep.children .bank).outputs (.readValue 0) =
      contractState .cpuregs (registerIndex (hierStep.inputs .decoded_rs1)) := by
    have held := Silean.Modules.RegisterBank.readValue_of_allowed
      bankMatches.allowed 0
    simpa [registerIndex, Silean.HierStep.childOutputs, Silean.Wiring.childInputValues,
      body, wiring, context, instancePorts,
      Silean.EndpointContext.moduleInput, Silean.SignalSource.value] using held
  have bankRead2Value : (hierStep.children .bank).outputs (.readValue 1) =
      contractState .cpuregs (registerIndex (hierStep.inputs .decoded_rs2)) := by
    have held := Silean.Modules.RegisterBank.readValue_of_allowed
      bankMatches.allowed 1
    simpa [registerIndex, Silean.HierStep.childOutputs, Silean.Wiring.childInputValues,
      body, wiring, context, instancePorts,
      Silean.EndpointContext.moduleInput, Silean.SignalSource.value] using held
  have rs1MuxValue : (hierStep.children .rs1Mux).outputs .result =
      bif (hierStep.children .rs1Zero).outputs .result then
        (hierStep.children .zeroWord).outputs .output else
        (hierStep.children .bank).outputs (.readValue 0) := by
    have held := Silean.Modules.Mux.result_of_allowed wordType rs1MuxMatch.allowed
    simpa [Silean.HierStep.childOutputs, Silean.Wiring.childInputValues, body, wiring, context, instancePorts,
      Silean.EndpointContext.instanceOutput, Silean.SignalSource.value] using held
  have rs2MuxValue : (hierStep.children .rs2Mux).outputs .result =
      bif (hierStep.children .rs2Zero).outputs .result then
        (hierStep.children .zeroWord).outputs .output else
        (hierStep.children .bank).outputs (.readValue 1) := by
    have held := Silean.Modules.Mux.result_of_allowed wordType rs2MuxMatch.allowed
    simpa [Silean.HierStep.childOutputs, Silean.Wiring.childInputValues, body, wiring, context, instancePorts,
      Silean.EndpointContext.instanceOutput, Silean.SignalSource.value] using held

  have readPath (address : RegisterAddress) (zeroTest : Bool) (bankValue : Word)
      (zeroEquation : zeroTest = addressType.equal address zeroAddressValue)
      (bankEquation : bankValue = contractState .cpuregs (registerIndex address)) :
      (bif zeroTest then zeroWord else bankValue) =
        readRegister address (contractState .cpuregs) := by
    by_cases isZero : address = zeroAddressValue
    · subst address
      have equalTrue : addressType.equal zeroAddressValue zeroAddressValue = true :=
        (addressType.equal_eq_true_iff _ _).mpr rfl
      have zeroIndex : registerIndex zeroAddressValue = 0 := by
        apply (registerIndex_eq_zero_iff zeroAddressValue).mpr
        rfl
      rw [zeroEquation, equalTrue]
      change zeroWord = readRegister zeroAddressValue (contractState .cpuregs)
      rw [readRegister]
      simp [zeroIndex]
    · have equalFalse : addressType.equal address zeroAddressValue = false := by
        cases equalResult : addressType.equal address zeroAddressValue
        · rfl
        · exact False.elim (isZero ((addressType.equal_eq_true_iff _ _).mp equalResult))
      have indexNonzero : registerIndex address ≠ 0 := by
        intro indexZero
        exact isZero ((registerIndex_eq_zero_iff address).mp indexZero)
      rw [zeroEquation, equalFalse, bankEquation,
        readRegister_nonzero address (contractState .cpuregs) indexNonzero]
      rfl

  let nextContractState := stateRule.apply hierStep.inputs contractState
  have boundaryRs1 : hierStep.outputs .cpuregs_rs1 =
      (hierStep.children .rs1Mux).outputs .result := by
    simpa [Silean.HierStep.childOutputs, body,
      wiring, context, Silean.EndpointContext.instanceOutput, Silean.SignalSource.value] using
        satisfies.1 .cpuregs_rs1
  have boundaryRs2 : hierStep.outputs .cpuregs_rs2 =
      (hierStep.children .rs2Mux).outputs .result := by
    simpa [Silean.HierStep.childOutputs, body,
      wiring, context, Silean.EndpointContext.instanceOutput, Silean.SignalSource.value] using
        satisfies.1 .cpuregs_rs2
  refine ⟨nextContractState, ?_, ?_⟩
  · constructor
    · intro rule
      dsimp only
      cases rule with
      | cpuregs_rs1 =>
          rw [cpuregsRs1Rule_holds_iff]
          rw [boundaryRs1, rs1MuxValue, zeroWordValueEq, zeroWordsEqual]
          exact readPath (hierStep.inputs .decoded_rs1) _ _ rs1ZeroValue bankRead1Value
      | cpuregs_rs2 =>
          rw [cpuregsRs2Rule_holds_iff]
          rw [boundaryRs2, rs2MuxValue, zeroWordValueEq, zeroWordsEqual]
          exact readPath (hierStep.inputs .decoded_rs2) _ _ rs2ZeroValue bankRead2Value
    · rfl
  · change (layerChildren .bank).certification.stateCorresponds
      (fun | .entries => nextContractState .cpuregs)
      (Silean.HierStep.nextState (layerChildren .bank).moduleStructure
        (hierStep.children .bank))
    rw [show (fun | Silean.Modules.RegisterBank.State.entries => nextContractState .cpuregs) =
        (childContracts .bank).stateRule.apply
          (body.wiring.childInputValues hierStep.inputs hierStep.childOutputs .bank)
          (fun | .entries => contractState .cpuregs) by
      funext bankState
      cases bankState
      change nextRegisters (hierStep.inputs .resetn) (hierStep.inputs .cpuregs_write)
          (hierStep.inputs .latched_rd) (hierStep.inputs .cpuregs_wrdata) (contractState .cpuregs) =
        Silean.Modules.RegisterBank.nextEntries 5 ((hierStep.children .enabledWrite).outputs .output)
          (hierStep.inputs .latched_rd) (hierStep.inputs .cpuregs_wrdata) (contractState .cpuregs)
      funext index
      rw [enabledWriteValue]
      unfold nextRegisters Silean.Modules.RegisterBank.nextEntries
      have nonzeroBool : (!addressType.equal (hierStep.inputs .latched_rd) zeroAddressValue) =
          decide (registerIndex (hierStep.inputs .latched_rd) ≠ 0) := by
        let address : RegisterAddress := hierStep.inputs .latched_rd
        change (!addressType.equal address zeroAddressValue) =
          decide (registerIndex address ≠ 0)
        by_cases nonzero : registerIndex address ≠ 0
        · have notEqual : address ≠ zeroAddressValue := by
            intro equal
            apply nonzero
            apply (registerIndex_eq_zero_iff address).mpr
            exact equal
          have equalFalse : addressType.equal address zeroAddressValue = false := by
            cases value : addressType.equal address zeroAddressValue
            · rfl
            · exact False.elim (notEqual ((addressType.equal_eq_true_iff _ _).mp value))
          simp [nonzero, equalFalse]
        · have zero : address = zeroAddressValue := by
            have indexZero : registerIndex address = 0 :=
              Decidable.not_not.mp nonzero
            have falseVector := (registerIndex_eq_zero_iff address).mp indexZero
            exact falseVector
          have equalTrue : addressType.equal address zeroAddressValue = true :=
            (addressType.equal_eq_true_iff _ _).mpr zero
          simp [nonzero, equalTrue]
      rw [nonzeroBool]
      rfl]
    exact bankMatches.nextCorresponds

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

end PicoRV.Regs
