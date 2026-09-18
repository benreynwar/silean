import Silean.Examples.PicoRV.Regs
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Mux.Internal.MuxVerification
import Silean.Modules.RegisterBank.RegisterBankTheorems
import Silean.Modules.Equality.EqualityTheorems

/-! # PicoRV register-file verification

Child certifications, schedules, structural state correspondence, and the
native `HierStep` implementation proof live here. Downstream proofs should
import `RegsTheorems`.
-/

namespace Silean.Examples.PicoRV.Regs

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts for body where
  bank := Modules.RegisterBank.certification wordType 5 2,
  zeroAddress := Modules.Constant.certification addressType zeroAddressValue,
  zeroWord := Modules.Constant.certification wordType zeroWordValue,
  rs1Zero := Modules.Equality.certification addressType,
  rs2Zero := Modules.Equality.certification addressType,
  rdZero := Modules.Equality.certification addressType,
  rdNonzero := Primitives.notCertified.certification,
  requestedWrite := Primitives.andCertified.certification,
  enabledWrite := Primitives.andCertified.certification,
  rs1Mux := Modules.Mux.certification wordType,
  rs2Mux := Modules.Mux.certification wordType

/-! ## Cycle certification -/

module_rule_schedules derivedRuleSchedules for body with childContracts
    implementing cycleContract where
  output
    | .cpuregs_rs1 => [.zeroAddress => Primitives.ConstantRule.apply,
        .zeroWord => Primitives.ConstantRule.apply,
        .rs1Zero => Modules.Equality.Rule.apply,
        .bank => Modules.RegisterBank.Rule.read 0,
        .rs1Mux => Modules.Mux.Rule.select]
    | .cpuregs_rs2 => [.zeroAddress => Primitives.ConstantRule.apply,
        .zeroWord => Primitives.ConstantRule.apply,
        .rs2Zero => Modules.Equality.Rule.apply,
        .bank => Modules.RegisterBank.Rule.read 1,
        .rs2Mux => Modules.Mux.Rule.select]
  state := [.zeroAddress => Primitives.ConstantRule.apply,
    .rdZero => Modules.Equality.Rule.apply,
    .rdNonzero => Primitives.NotRule.apply,
    .requestedWrite => Primitives.AndRule.apply,
    .enabledWrite => Primitives.AndRule.apply]

section LayerCertification

variable (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
  body childContracts)

private def stateCorresponds (contractState : cycleContract.state.Values)
    (structuralState :
      (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren).State) : Prop :=
  (layerChildren .bank).certification.stateCorresponds
    (fun | .entries => contractState .cpuregs) (structuralState .bank)

private theorem hasCorrespondingState
    (structuralState :
      (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren).State) :
    ∃ contractState, stateCorresponds layerChildren contractState structuralState := by
  rcases (layerChildren .bank).certification.hasCorrespondingState
      (structuralState .bank) with
    ⟨bankState, bankCorresponds⟩
  exact ⟨fun | .cpuregs => bankState .entries, bankCorresponds⟩

private theorem implements :
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro contractState hierStep corresponds satisfies
  have statelessMatch (child : Instance)
      [Subsingleton (childContracts child).state.Values]
      (state : (childContracts child).state.Values) :=
    Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren hierStep satisfies child state
  have zeroAddressMatch := statelessMatch .zeroAddress SignalMap.emptyValues
  have zeroWordMatch := statelessMatch .zeroWord SignalMap.emptyValues
  have rs1ZeroMatch := statelessMatch .rs1Zero SignalMap.emptyValues
  have rs2ZeroMatch := statelessMatch .rs2Zero SignalMap.emptyValues
  have rdZeroMatch := statelessMatch .rdZero SignalMap.emptyValues
  have emptyStateSubsingleton : Subsingleton emptySignalMap.Values := inferInstance
  have rdNonzeroMatch :=
    letI : Subsingleton (childContracts .rdNonzero).state.Values := by
      change Subsingleton emptySignalMap.Values
      exact emptyStateSubsingleton
    statelessMatch .rdNonzero SignalMap.emptyValues
  have requestedWriteMatch :=
    letI : Subsingleton (childContracts .requestedWrite).state.Values := by
      change Subsingleton emptySignalMap.Values
      exact emptyStateSubsingleton
    statelessMatch .requestedWrite SignalMap.emptyValues
  have enabledWriteMatch :=
    letI : Subsingleton (childContracts .enabledWrite).state.Values := by
      change Subsingleton emptySignalMap.Values
      exact emptyStateSubsingleton
    statelessMatch .enabledWrite SignalMap.emptyValues
  have rs1MuxMatch :=
    letI : Subsingleton (childContracts .rs1Mux).state.Values := by
      change Subsingleton emptySignalMap.Values
      exact emptyStateSubsingleton
    statelessMatch .rs1Mux SignalMap.emptyValues
  have rs2MuxMatch :=
    letI : Subsingleton (childContracts .rs2Mux).state.Values := by
      change Subsingleton emptySignalMap.Values
      exact emptyStateSubsingleton
    statelessMatch .rs2Mux SignalMap.emptyValues
  have bankMatches := Contracts.Cycle.Certification.Layer.childSolutionMatchesContract
    layerChildren hierStep satisfies .bank
    (fun | .entries => contractState .cpuregs) corresponds

  have zeroAddressValueEq : (hierStep.children .zeroAddress).outputs .output = zeroAddressValue :=
    (Modules.Constant.outputRule_holds_iff addressType zeroAddressValue _ _ _).mp
      (zeroAddressMatch.ruleHolds Primitives.ConstantRule.apply)
  have zeroWordValueEq : (hierStep.children .zeroWord).outputs .output = zeroWordValue :=
    (Modules.Constant.outputRule_holds_iff wordType zeroWordValue _ _ _).mp
      (zeroWordMatch.ruleHolds Primitives.ConstantRule.apply)
  have zeroWordsEqual : zeroWordValue = zeroWord := rfl
  have rs1ZeroValue : (hierStep.children .rs1Zero).outputs .result =
      addressType.equal (hierStep.inputs .decoded_rs1) zeroAddressValue := by
    have held := (Modules.Equality.outputRule_holds_iff addressType _ _ _).mp
      (rs1ZeroMatch.ruleHolds Modules.Equality.Rule.apply)
    have wired : (hierStep.children .rs1Zero).outputs .result =
        addressType.equal (hierStep.inputs .decoded_rs1) ((hierStep.children .zeroAddress).outputs .output) := by
      simpa [HierStep.childOutputs, Wiring.childInputValues, body, wiring, context, instancePorts,
        EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] using held
    rw [zeroAddressValueEq] at wired
    exact wired
  have rs2ZeroValue : (hierStep.children .rs2Zero).outputs .result =
      addressType.equal (hierStep.inputs .decoded_rs2) zeroAddressValue := by
    have held := (Modules.Equality.outputRule_holds_iff addressType _ _ _).mp
      (rs2ZeroMatch.ruleHolds Modules.Equality.Rule.apply)
    have wired : (hierStep.children .rs2Zero).outputs .result =
        addressType.equal (hierStep.inputs .decoded_rs2) ((hierStep.children .zeroAddress).outputs .output) := by
      simpa [HierStep.childOutputs, Wiring.childInputValues, body, wiring, context, instancePorts,
        EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] using held
    rw [zeroAddressValueEq] at wired
    exact wired
  have rdZeroValue : (hierStep.children .rdZero).outputs .result =
      addressType.equal (hierStep.inputs .latched_rd) zeroAddressValue := by
    have held := (Modules.Equality.outputRule_holds_iff addressType _ _ _).mp
      (rdZeroMatch.ruleHolds Modules.Equality.Rule.apply)
    have wired : (hierStep.children .rdZero).outputs .result =
        addressType.equal (hierStep.inputs .latched_rd) ((hierStep.children .zeroAddress).outputs .output) := by
      simpa [HierStep.childOutputs, Wiring.childInputValues, body, wiring, context, instancePorts,
        EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] using held
    rw [zeroAddressValueEq] at wired
    exact wired
  have rdNonzeroValue : (hierStep.children .rdNonzero).outputs .output =
      !addressType.equal (hierStep.inputs .latched_rd) zeroAddressValue := by
    have held := (Primitives.notOutputRule_holds_iff _ _ _).mp
      (rdNonzeroMatch.ruleHolds Primitives.NotRule.apply)
    normalize_child_hyp held unfolding wiring, context
    exact held.trans (congrArg Bool.not rdZeroValue)
  have requestedWriteValue : (hierStep.children .requestedWrite).outputs .output =
      (hierStep.inputs .resetn && hierStep.inputs .cpuregs_write) := by
    have held := (Primitives.andOutputRule_holds_iff _ _ _).mp
      (requestedWriteMatch.ruleHolds Primitives.AndRule.apply)
    simpa [HierStep.childOutputs, Wiring.childInputValues, body, wiring, context, instancePorts,
      EndpointContext.moduleInput, SignalSource.value] using held
  have enabledWriteValue : (hierStep.children .enabledWrite).outputs .output =
      ((hierStep.inputs .resetn && hierStep.inputs .cpuregs_write) &&
        !addressType.equal (hierStep.inputs .latched_rd) zeroAddressValue) := by
    have held := (Primitives.andOutputRule_holds_iff _ _ _).mp
      (enabledWriteMatch.ruleHolds Primitives.AndRule.apply)
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
    have held := (Modules.RegisterBank.readRule_holds_iff wordType 5 2 0 _ _ _).mp
      (bankMatches.ruleHolds (.read 0))
    simpa [registerIndex, HierStep.childOutputs, Wiring.childInputValues,
      body, wiring, context, instancePorts,
      EndpointContext.moduleInput, SignalSource.value] using held
  have bankRead2Value : (hierStep.children .bank).outputs (.readValue 1) =
      contractState .cpuregs (registerIndex (hierStep.inputs .decoded_rs2)) := by
    have held := (Modules.RegisterBank.readRule_holds_iff wordType 5 2 1 _ _ _).mp
      (bankMatches.ruleHolds (.read 1))
    simpa [registerIndex, HierStep.childOutputs, Wiring.childInputValues,
      body, wiring, context, instancePorts,
      EndpointContext.moduleInput, SignalSource.value] using held
  have rs1MuxValue : (hierStep.children .rs1Mux).outputs .result =
      bif (hierStep.children .rs1Zero).outputs .result then
        (hierStep.children .zeroWord).outputs .output else
        (hierStep.children .bank).outputs (.readValue 0) := by
    have held := (Modules.Mux.selectRule_holds_iff wordType _ _ _).mp
      (rs1MuxMatch.ruleHolds Modules.Mux.Rule.select)
    simpa [HierStep.childOutputs, Wiring.childInputValues, body, wiring, context, instancePorts,
      EndpointContext.instanceOutput, SignalSource.value] using held
  have rs2MuxValue : (hierStep.children .rs2Mux).outputs .result =
      bif (hierStep.children .rs2Zero).outputs .result then
        (hierStep.children .zeroWord).outputs .output else
        (hierStep.children .bank).outputs (.readValue 1) := by
    have held := (Modules.Mux.selectRule_holds_iff wordType _ _ _).mp
      (rs2MuxMatch.ruleHolds Modules.Mux.Rule.select)
    simpa [HierStep.childOutputs, Wiring.childInputValues, body, wiring, context, instancePorts,
      EndpointContext.instanceOutput, SignalSource.value] using held

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
    simpa [HierStep.childOutputs, body,
      wiring, context, EndpointContext.instanceOutput, SignalSource.value] using
        satisfies.1 .cpuregs_rs1
  have boundaryRs2 : hierStep.outputs .cpuregs_rs2 =
      (hierStep.children .rs2Mux).outputs .result := by
    simpa [HierStep.childOutputs, body,
      wiring, context, EndpointContext.instanceOutput, SignalSource.value] using
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
      (HierStep.nextState (layerChildren .bank).moduleStructure
        (hierStep.children .bank))
    rw [show (fun | Modules.RegisterBank.State.entries => nextContractState .cpuregs) =
        (childContracts .bank).stateRule.apply
          (body.wiring.childInputValues hierStep.inputs hierStep.childOutputs .bank)
          (fun | .entries => contractState .cpuregs) by
      funext bankState
      cases bankState
      change nextRegisters (hierStep.inputs .resetn) (hierStep.inputs .cpuregs_write)
          (hierStep.inputs .latched_rd) (hierStep.inputs .cpuregs_wrdata) (contractState .cpuregs) =
        Modules.RegisterBank.nextEntries 5 ((hierStep.children .enabledWrite).outputs .output)
          (hierStep.inputs .latched_rd) (hierStep.inputs .cpuregs_wrdata) (contractState .cpuregs)
      funext index
      rw [enabledWriteValue]
      unfold nextRegisters Modules.RegisterBank.nextEntries
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

end Silean.Examples.PicoRV.Regs
