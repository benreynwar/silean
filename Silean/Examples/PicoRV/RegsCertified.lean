import Silean.Examples.PicoRV.Regs
import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Mux.MuxCertified
import Silean.Modules.RegisterBank.RegisterBankCertified

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
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have statelessMatch (child : Instance)
      [Subsingleton (childContracts child).state.Values]
      (state : (childContracts child).state.Values) :=
    Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies child state
  have zeroAddressEvaluates := (statelessMatch .zeroAddress SignalMap.emptyValues).1
  have zeroWordEvaluates := (statelessMatch .zeroWord SignalMap.emptyValues).1
  have rs1ZeroEvaluates := (statelessMatch .rs1Zero SignalMap.emptyValues).1
  have rs2ZeroEvaluates := (statelessMatch .rs2Zero SignalMap.emptyValues).1
  have rdZeroEvaluates := (statelessMatch .rdZero SignalMap.emptyValues).1
  have emptyStateSubsingleton : Subsingleton emptySignalMap.Values := inferInstance
  have rdNonzeroEvaluates :=
    letI : Subsingleton (childContracts .rdNonzero).state.Values := by
      change Subsingleton emptySignalMap.Values
      exact emptyStateSubsingleton
    (statelessMatch .rdNonzero SignalMap.emptyValues).1
  have requestedWriteEvaluates :=
    letI : Subsingleton (childContracts .requestedWrite).state.Values := by
      change Subsingleton emptySignalMap.Values
      exact emptyStateSubsingleton
    (statelessMatch .requestedWrite SignalMap.emptyValues).1
  have enabledWriteEvaluates :=
    letI : Subsingleton (childContracts .enabledWrite).state.Values := by
      change Subsingleton emptySignalMap.Values
      exact emptyStateSubsingleton
    (statelessMatch .enabledWrite SignalMap.emptyValues).1
  have rs1MuxEvaluates :=
    letI : Subsingleton (childContracts .rs1Mux).state.Values := by
      change Subsingleton emptySignalMap.Values
      exact emptyStateSubsingleton
    (statelessMatch .rs1Mux SignalMap.emptyValues).1
  have rs2MuxEvaluates :=
    letI : Subsingleton (childContracts .rs2Mux).state.Values := by
      change Subsingleton emptySignalMap.Values
      exact emptyStateSubsingleton
    (statelessMatch .rs2Mux SignalMap.emptyValues).1
  have bankMatches := Contracts.Cycle.Certification.Layer.childSolutionMatchesContract
    layerChildren inputs structuralState proposal satisfies .bank
    (fun | .entries => contractState .cpuregs) corresponds

  have zeroAddressValueEq : (proposal.2 .zeroAddress).outputs .output = zeroAddressValue :=
    (Modules.Constant.outputRule_holds_iff addressType zeroAddressValue _ _ _).mp
      (zeroAddressEvaluates.1 Primitives.ConstantRule.apply)
  have zeroWordValueEq : (proposal.2 .zeroWord).outputs .output = zeroWordValue :=
    (Modules.Constant.outputRule_holds_iff wordType zeroWordValue _ _ _).mp
      (zeroWordEvaluates.1 Primitives.ConstantRule.apply)
  have zeroWordsEqual : zeroWordValue = zeroWord := rfl
  have rs1ZeroValue : (proposal.2 .rs1Zero).outputs .result =
      addressType.equal (inputs .decoded_rs1) zeroAddressValue := by
    have held := (Modules.Equality.outputRule_holds_iff addressType _ _ _).mp
      (rs1ZeroEvaluates.1 Modules.Equality.Rule.apply)
    have wired : (proposal.2 .rs1Zero).outputs .result =
        addressType.equal (inputs .decoded_rs1) ((proposal.2 .zeroAddress).outputs .output) := by
      simpa [ProposedValues.childInputs, body, wiring, context, instancePorts,
        EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] using held
    rw [zeroAddressValueEq] at wired
    exact wired
  have rs2ZeroValue : (proposal.2 .rs2Zero).outputs .result =
      addressType.equal (inputs .decoded_rs2) zeroAddressValue := by
    have held := (Modules.Equality.outputRule_holds_iff addressType _ _ _).mp
      (rs2ZeroEvaluates.1 Modules.Equality.Rule.apply)
    have wired : (proposal.2 .rs2Zero).outputs .result =
        addressType.equal (inputs .decoded_rs2) ((proposal.2 .zeroAddress).outputs .output) := by
      simpa [ProposedValues.childInputs, body, wiring, context, instancePorts,
        EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] using held
    rw [zeroAddressValueEq] at wired
    exact wired
  have rdZeroValue : (proposal.2 .rdZero).outputs .result =
      addressType.equal (inputs .latched_rd) zeroAddressValue := by
    have held := (Modules.Equality.outputRule_holds_iff addressType _ _ _).mp
      (rdZeroEvaluates.1 Modules.Equality.Rule.apply)
    have wired : (proposal.2 .rdZero).outputs .result =
        addressType.equal (inputs .latched_rd) ((proposal.2 .zeroAddress).outputs .output) := by
      simpa [ProposedValues.childInputs, body, wiring, context, instancePorts,
        EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] using held
    rw [zeroAddressValueEq] at wired
    exact wired
  have rdNonzeroValue : (proposal.2 .rdNonzero).outputs .output =
      !addressType.equal (inputs .latched_rd) zeroAddressValue := by
    have held := (Primitives.notOutputRule_holds_iff _ _ _).mp
      (rdNonzeroEvaluates.1 Primitives.NotRule.apply)
    simpa [ProposedValues.childInputs, body, wiring, context, instancePorts,
      EndpointContext.instanceOutput, SignalSource.value, rdZeroValue] using held
  have requestedWriteValue : (proposal.2 .requestedWrite).outputs .output =
      (inputs .resetn && inputs .cpuregs_write) := by
    have held := (Primitives.andOutputRule_holds_iff _ _ _).mp
      (requestedWriteEvaluates.1 Primitives.AndRule.apply)
    simpa [ProposedValues.childInputs, body, wiring, context, instancePorts,
      EndpointContext.moduleInput, SignalSource.value] using held
  have enabledWriteValue : (proposal.2 .enabledWrite).outputs .output =
      ((inputs .resetn && inputs .cpuregs_write) &&
        !addressType.equal (inputs .latched_rd) zeroAddressValue) := by
    have held := (Primitives.andOutputRule_holds_iff _ _ _).mp
      (enabledWriteEvaluates.1 Primitives.AndRule.apply)
    simpa [ProposedValues.childInputs, body, wiring, context, instancePorts,
      EndpointContext.instanceOutput, SignalSource.value, requestedWriteValue,
      rdNonzeroValue] using held

  have bankRead1Value : (proposal.2 .bank).outputs (.readValue 0) =
      contractState .cpuregs (registerIndex (inputs .decoded_rs1)) := by
    have held := (Modules.RegisterBank.readRule_holds_iff wordType 5 2 0 _ _ _).mp
      (bankMatches.1.1 (.read 0))
    simpa [registerIndex, ProposedValues.childInputs, body, wiring, context, instancePorts,
      EndpointContext.moduleInput, SignalSource.value] using held
  have bankRead2Value : (proposal.2 .bank).outputs (.readValue 1) =
      contractState .cpuregs (registerIndex (inputs .decoded_rs2)) := by
    have held := (Modules.RegisterBank.readRule_holds_iff wordType 5 2 1 _ _ _).mp
      (bankMatches.1.1 (.read 1))
    simpa [registerIndex, ProposedValues.childInputs, body, wiring, context, instancePorts,
      EndpointContext.moduleInput, SignalSource.value] using held
  have rs1MuxValue : (proposal.2 .rs1Mux).outputs .result =
      bif (proposal.2 .rs1Zero).outputs .result then
        (proposal.2 .zeroWord).outputs .output else
        (proposal.2 .bank).outputs (.readValue 0) := by
    have held := (Modules.Mux.selectRule_holds_iff wordType _ _ _).mp
      (rs1MuxEvaluates.1 Modules.Mux.Rule.select)
    simpa [ProposedValues.childInputs, body, wiring, context, instancePorts,
      EndpointContext.instanceOutput, SignalSource.value] using held
  have rs2MuxValue : (proposal.2 .rs2Mux).outputs .result =
      bif (proposal.2 .rs2Zero).outputs .result then
        (proposal.2 .zeroWord).outputs .output else
        (proposal.2 .bank).outputs (.readValue 1) := by
    have held := (Modules.Mux.selectRule_holds_iff wordType _ _ _).mp
      (rs2MuxEvaluates.1 Modules.Mux.Rule.select)
    simpa [ProposedValues.childInputs, body, wiring, context, instancePorts,
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

  let nextContractState := stateRule.apply inputs contractState
  have boundaryRs1 : proposal.outputs .cpuregs_rs1 =
      (proposal.2 .rs1Mux).outputs .result := by
    simpa [ProposedValues.outputs, ProposedValues.boundaryOutputsSatisfy, body,
      wiring, context, EndpointContext.instanceOutput, SignalSource.value] using
        satisfies.1 .cpuregs_rs1
  have boundaryRs2 : proposal.outputs .cpuregs_rs2 =
      (proposal.2 .rs2Mux).outputs .result := by
    simpa [ProposedValues.outputs, ProposedValues.boundaryOutputsSatisfy, body,
      wiring, context, EndpointContext.instanceOutput, SignalSource.value] using
        satisfies.1 .cpuregs_rs2
  refine ⟨nextContractState, ?_, ?_⟩
  · constructor
    · intro rule
      cases rule with
      | cpuregs_rs1 =>
          rw [cpuregsRs1Rule_holds_iff]
          rw [boundaryRs1, rs1MuxValue, zeroWordValueEq, zeroWordsEqual]
          exact readPath (inputs .decoded_rs1) _ _ rs1ZeroValue bankRead1Value
      | cpuregs_rs2 =>
          rw [cpuregsRs2Rule_holds_iff]
          rw [boundaryRs2, rs2MuxValue, zeroWordValueEq, zeroWordsEqual]
          exact readPath (inputs .decoded_rs2) _ _ rs2ZeroValue bankRead2Value
    · rfl
  · change (layerChildren .bank).certification.stateCorresponds
      (fun | .entries => nextContractState .cpuregs) (proposal.2 .bank).nextState
    rw [show (fun | Modules.RegisterBank.State.entries => nextContractState .cpuregs) =
        (childContracts .bank).stateRule.apply
          (ProposedValues.childInputs body
            (fun child => (layerChildren child).moduleStructure) inputs proposal.2 .bank)
          (fun | .entries => contractState .cpuregs) by
      funext bankState
      cases bankState
      change nextRegisters (inputs .resetn) (inputs .cpuregs_write)
          (inputs .latched_rd) (inputs .cpuregs_wrdata) (contractState .cpuregs) =
        Modules.RegisterBank.nextEntries 5 ((proposal.2 .enabledWrite).outputs .output)
          (inputs .latched_rd) (inputs .cpuregs_wrdata) (contractState .cpuregs)
      funext index
      rw [enabledWriteValue]
      unfold nextRegisters Modules.RegisterBank.nextEntries
      have nonzeroBool : (!addressType.equal (inputs .latched_rd) zeroAddressValue) =
          decide (registerIndex (inputs .latched_rd) ≠ 0) := by
        let address : RegisterAddress := inputs .latched_rd
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
    exact bankMatches.2

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

/-- The register-file hierarchy and every module below it have concrete structure. -/
theorem hasExactlyOneSolution (inputs : ports.inputs.Values)
    (currentState : moduleStructure.State) :
    ∃ proposal, moduleStructure.IsSolution inputs currentState proposal ∧
      ∀ other, moduleStructure.IsSolution inputs currentState other → other = proposal :=
  certified.hasExactlyOneStructuralResult inputs currentState

end Silean.Examples.PicoRV.Regs
