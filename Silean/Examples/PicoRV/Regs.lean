import Silean.Foundation.BitVector
import Silean.Contracts.Cycle.CycleEvaluation
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Modules.Constant
import Silean.Modules.Equality
import Silean.Modules.Mux
import Silean.Modules.RegisterBank
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.And
import Silean.Primitives.NotPrimitive

namespace Silean.Examples.PicoRV.Regs

open Silean
open Contracts.Cycle.Certification.Layer

/-! PicoRV32's 32-entry integer register file. Register zero always reads as
zero and ignores writes. The exact cycle contract is followed by a structural
implementation around the generic two-read `RegisterBank`. -/

abbrev Word := Fin 32 → Bool
abbrev RegisterAddress := Fin 5 → Bool
abbrev RegisterValues := Fin 32 → Word

inductive Input
  | resetn
  | decoded_rs1
  | decoded_rs2
  | cpuregs_write
  | latched_rd
  | cpuregs_wrdata
deriving Enumeration

inductive Output
  | cpuregs_rs1
  | cpuregs_rs2
deriving Enumeration

@[reducible] def inputMap : SignalMap :=
  EnumeratedMap.of Input fun
    | .resetn | .cpuregs_write => .bit
    | .decoded_rs1 | .decoded_rs2 | .latched_rd => .vector 5 .bit
    | .cpuregs_wrdata => .vector 32 .bit

@[reducible] def outputMap : SignalMap :=
  EnumeratedMap.of Output fun
    | .cpuregs_rs1 | .cpuregs_rs2 => .vector 32 .bit

@[reducible] def ports : ModulePorts := ⟨inputMap, outputMap⟩

inductive State
  /-- The 32 architectural integer registers. -/
  | cpuregs
deriving Enumeration

@[reducible] def stateMap : SignalMap :=
  EnumeratedMap.of State fun
    | .cpuregs => .vector 32 (.vector 32 .bit)

def zeroWord : Word := fun _ => false

def registerIndex (address : RegisterAddress) : Fin 32 :=
  BitVector.toIndex 5 address

@[simp] theorem registerIndex_eq_zero_iff (address : RegisterAddress) :
    registerIndex address = 0 ↔ address = fun _ => false := by
  constructor
  · intro equal
    apply BitVector.toNat_injective 5
    have valuesEqual := congrArg Fin.val equal
    simpa [registerIndex, BitVector.toIndex_val] using valuesEqual
  · rintro rfl
    apply Fin.ext
    simp [registerIndex, BitVector.toIndex_val]

def readRegister (address : RegisterAddress) (registers : RegisterValues) : Word :=
  if registerIndex address = 0 then zeroWord else registers (registerIndex address)

def nextRegisters (resetn cpuregs_write : Bool)
    (latched_rd : RegisterAddress) (cpuregs_wrdata : Word)
    (registers : RegisterValues) : RegisterValues :=
  fun index =>
    if resetn && cpuregs_write && decide (registerIndex latched_rd ≠ 0) &&
        decide (index = registerIndex latched_rd)
    then cpuregs_wrdata
    else registers index

inductive Rule
  | cpuregs_rs1
  | cpuregs_rs2
deriving Enumeration

def cpuregsRs1Rule :
    Contracts.Cycle.CycleOutputRule ports stateMap
      { inputTypes := .cons (.vector 5 .bit) .nil
        outputTypes := .cons (.vector 32 .bit) .nil } where
  readsInputs := inputMap.select .decoded_rs1
  writesOutputs := outputMap.select .cpuregs_rs1
  target
    | (decoded_rs1, ()), state =>
        (readRegister decoded_rs1 (state .cpuregs), ())

def cpuregsRs2Rule :
    Contracts.Cycle.CycleOutputRule ports stateMap
      { inputTypes := .cons (.vector 5 .bit) .nil
        outputTypes := .cons (.vector 32 .bit) .nil } where
  readsInputs := inputMap.select .decoded_rs2
  writesOutputs := outputMap.select .cpuregs_rs2
  target
    | (decoded_rs2, ()), state =>
        (readRegister decoded_rs2 (state .cpuregs), ())

def stateRule : Contracts.Cycle.CycleStateRule ports stateMap where
  inputTypes := .cons .bit
    (.cons .bit (.cons (.vector 5 .bit) (.cons (.vector 32 .bit) .nil)))
  readsInputs := ((((inputMap.select .cpuregs_wrdata).prepend .latched_rd).prepend
    .cpuregs_write).prepend .resetn)
  target
    | (resetn, (cpuregs_write, (latched_rd, (cpuregs_wrdata, ())))), state =>
        fun
          | .cpuregs => nextRegisters resetn cpuregs_write latched_rd
              cpuregs_wrdata (state .cpuregs)

@[reducible] def cycleContract : Contracts.Cycle.ModuleCycleContract ports where
  state := stateMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule
    | .cpuregs_rs1 => ⟨_, cpuregsRs1Rule⟩
    | .cpuregs_rs2 => ⟨_, cpuregsRs2Rule⟩
  stateRule := stateRule
  outputCoverage := by rfl

@[simp] theorem readRegister_zero (registers : RegisterValues) :
    readRegister (fun _ => false) registers = zeroWord := by
  have zeroIndex : registerIndex (fun _ => false) = 0 := by
    apply Fin.ext
    simp [registerIndex, BitVector.toIndex_val]
  simp [readRegister, zeroIndex]

theorem readRegister_nonzero (address : RegisterAddress)
    (registers : RegisterValues) (nonzero : registerIndex address ≠ 0) :
    readRegister address registers = registers (registerIndex address) := by
  simp [readRegister, nonzero]

@[simp] theorem nextRegisters_reset (cpuregs_write : Bool)
    (latched_rd : RegisterAddress) (cpuregs_wrdata : Word)
    (registers : RegisterValues) :
    nextRegisters false cpuregs_write latched_rd cpuregs_wrdata registers = registers := by
  funext index
  simp [nextRegisters]

@[simp] theorem nextRegisters_write_disabled (resetn : Bool)
    (latched_rd : RegisterAddress) (cpuregs_wrdata : Word)
    (registers : RegisterValues) :
    nextRegisters resetn false latched_rd cpuregs_wrdata registers = registers := by
  funext index
  simp [nextRegisters]

theorem nextRegisters_zero (resetn cpuregs_write : Bool)
    (latched_rd : RegisterAddress) (cpuregs_wrdata : Word)
    (registers : RegisterValues) (zero : registerIndex latched_rd = 0) :
    nextRegisters resetn cpuregs_write latched_rd cpuregs_wrdata registers = registers := by
  funext index
  simp [nextRegisters, zero]

@[simp] theorem nextRegisters_written (latched_rd : RegisterAddress)
    (cpuregs_wrdata : Word) (registers : RegisterValues)
    (nonzero : registerIndex latched_rd ≠ 0) :
    nextRegisters true true latched_rd cpuregs_wrdata registers
      (registerIndex latched_rd) = cpuregs_wrdata := by
  simp [nextRegisters, nonzero]

theorem nextRegisters_other (resetn cpuregs_write : Bool)
    (latched_rd : RegisterAddress) (cpuregs_wrdata : Word)
    (registers : RegisterValues) (index : Fin 32)
    (different : index ≠ registerIndex latched_rd) :
    nextRegisters resetn cpuregs_write latched_rd cpuregs_wrdata registers index =
      registers index := by
  simp [nextRegisters, different]

@[simp] theorem cpuregsRs1Rule_holds_iff
    (inputs : ports.inputs.Values) (state : stateMap.Values)
    (outputs : ports.outputs.Values) :
    cpuregsRs1Rule.Holds inputs state outputs ↔
      outputs .cpuregs_rs1 = readRegister (inputs .decoded_rs1) (state .cpuregs) := by
  simp [cpuregsRs1Rule, Contracts.Cycle.CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select]

@[simp] theorem cpuregsRs2Rule_holds_iff
    (inputs : ports.inputs.Values) (state : stateMap.Values)
    (outputs : ports.outputs.Values) :
    cpuregsRs2Rule.Holds inputs state outputs ↔
      outputs .cpuregs_rs2 = readRegister (inputs .decoded_rs2) (state .cpuregs) := by
  simp [cpuregsRs2Rule, Contracts.Cycle.CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select]

/-! ## Hardware structure -/

private inductive Instance
  /-- The shared 32-entry storage with two independent read ports. -/
  | bank
  /-- Shared constant address zero for the three address comparisons. -/
  | zeroAddress
  /-- Shared constant word zero for both architectural `x0` read results. -/
  | zeroWord
  /-- Tests the first read address for architectural register zero. -/
  | rs1Zero
  /-- Tests the second read address for architectural register zero. -/
  | rs2Zero
  /-- Tests the write address for architectural register zero. -/
  | rdZero
  /-- Inverts the write-address-zero result. -/
  | rdNonzero
  /-- Requires both an active reset signal and a write request. -/
  | requestedWrite
  /-- Suppresses writes to architectural register zero. -/
  | enabledWrite
  /-- Selects zero or the stored value for the first read port. -/
  | rs1Mux
  /-- Selects zero or the stored value for the second read port. -/
  | rs2Mux
deriving Enumeration

private abbrev wordType : SignalType := .vector 32 .bit
private abbrev addressType : SignalType := .vector 5 .bit

@[reducible] private def instancePorts : InstancePorts :=
  EnumeratedMap.of Instance fun
    | .bank => Modules.RegisterBank.ports wordType 5 2
    | .zeroAddress => Modules.Constant.ports addressType
    | .zeroWord => Modules.Constant.ports wordType
    | .rs1Zero | .rs2Zero | .rdZero => Modules.Equality.ports addressType
    | .rdNonzero => Primitives.not.ports
    | .requestedWrite | .enabledWrite => Primitives.and.ports
    | .rs1Mux | .rs2Mux => Modules.Mux.ports wordType

@[reducible] private def context : EndpointContext where
  ports := ports
  instancePorts := instancePorts

private def wiring : Wiring context.ports context.instancePorts :=
  { moduleOutput := fun
    -- Architectural reads are the two zero-protected mux results.
    | .cpuregs_rs1 => context.instanceOutput .rs1Mux .result
    | .cpuregs_rs2 => context.instanceOutput .rs2Mux .result
    instanceInput := fun
    -- The shared bank sees both decoded source addresses.
    | .bank, .readAddress 0 => context.moduleInput .decoded_rs1
    | .bank, .readAddress 1 => context.moduleInput .decoded_rs2
    -- Its synchronous write port uses the filtered write enable.
    | .bank, .writeEnable => context.instanceOutput .enabledWrite .output
    | .bank, .writeAddress => context.moduleInput .latched_rd
    | .bank, .writeValue => context.moduleInput .cpuregs_wrdata
    -- Both constants are closed sources.
    | .zeroAddress, impossible => nomatch impossible
    | .zeroWord, impossible => nomatch impossible
    -- Compare each externally supplied address with the shared zero address.
    | .rs1Zero, .left => context.moduleInput .decoded_rs1
    | .rs1Zero, .right => context.instanceOutput .zeroAddress .output
    | .rs2Zero, .left => context.moduleInput .decoded_rs2
    | .rs2Zero, .right => context.instanceOutput .zeroAddress .output
    | .rdZero, .left => context.moduleInput .latched_rd
    | .rdZero, .right => context.instanceOutput .zeroAddress .output
    -- Form resetn && cpuregs_write && (latched_rd != 0).
    | .rdNonzero, .input => context.instanceOutput .rdZero .result
    | .requestedWrite, .left => context.moduleInput .resetn
    | .requestedWrite, .right => context.moduleInput .cpuregs_write
    | .enabledWrite, .left => context.instanceOutput .requestedWrite .output
    | .enabledWrite, .right => context.instanceOutput .rdNonzero .output
    -- A zero address selects the shared zero word; otherwise select the bank.
    | .rs1Mux, .select => context.instanceOutput .rs1Zero .result
    | .rs1Mux, .whenFalse => context.instanceOutput .bank (.readValue 0)
    | .rs1Mux, .whenTrue => context.instanceOutput .zeroWord .output
    | .rs2Mux, .select => context.instanceOutput .rs2Zero .result
    | .rs2Mux, .whenFalse => context.instanceOutput .bank (.readValue 1)
    | .rs2Mux, .whenTrue => context.instanceOutput .zeroWord .output }

@[reducible] private def body : ModuleBody := ⟨context, wiring⟩

private def zeroAddressValue : addressType.Denote := fun _ => false
private def zeroWordValue : wordType.Denote := fun _ => false

@[reducible] private def childContracts : Contracts.Cycle.ChildCycleContracts body
  | .bank => Modules.RegisterBank.cycleContract wordType 5 2
  | .zeroAddress => Modules.Constant.cycleContract addressType zeroAddressValue
  | .zeroWord => Modules.Constant.cycleContract wordType zeroWordValue
  | .rs1Zero | .rs2Zero | .rdZero => Modules.Equality.cycleContract addressType
  | .rdNonzero => Primitives.notCycleContract
  | .requestedWrite | .enabledWrite => Primitives.andCycleContract
  | .rs1Mux | .rs2Mux => Modules.Mux.cycleContract wordType

@[reducible] private def structuralChildren :
    (name : instancePorts.Name) → ModuleStructure (instancePorts.ports name)
  | .bank => Modules.RegisterBank.moduleStructure wordType 5 2
  | .zeroAddress => Modules.Constant.moduleStructure addressType zeroAddressValue
  | .zeroWord => Modules.Constant.moduleStructure wordType zeroWordValue
  | .rs1Zero | .rs2Zero | .rdZero => Modules.Equality.moduleStructure addressType
  | .rdNonzero => Primitives.notCertified.moduleStructure
  | .requestedWrite | .enabledWrite => Primitives.andCertified.moduleStructure
  | .rs1Mux | .rs2Mux => Modules.Mux.moduleStructure wordType

/-- The concrete PicoRV32 register-file hierarchy. -/
def moduleStructure : ModuleStructure ports :=
  .composite body structuralChildren

/-! ## Cycle certification -/

private abbrev bankRead (port : Fin 2) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence body childContracts :=
  ⟨.bank, Modules.RegisterBank.Rule.read port⟩

private abbrev zeroAddressRule :
    Contracts.Cycle.Certification.Layer.RuleOccurrence body childContracts :=
  ⟨.zeroAddress, Primitives.ConstantRule.apply⟩

private abbrev zeroWordRule :
    Contracts.Cycle.Certification.Layer.RuleOccurrence body childContracts :=
  ⟨.zeroWord, Primitives.ConstantRule.apply⟩

private abbrev rs1ZeroRule :
    Contracts.Cycle.Certification.Layer.RuleOccurrence body childContracts :=
  ⟨.rs1Zero, Modules.Equality.Rule.apply⟩

private abbrev rs2ZeroRule :
    Contracts.Cycle.Certification.Layer.RuleOccurrence body childContracts :=
  ⟨.rs2Zero, Modules.Equality.Rule.apply⟩

private abbrev rdZeroRule :
    Contracts.Cycle.Certification.Layer.RuleOccurrence body childContracts :=
  ⟨.rdZero, Modules.Equality.Rule.apply⟩

private abbrev rdNonzeroRule :
    Contracts.Cycle.Certification.Layer.RuleOccurrence body childContracts :=
  ⟨.rdNonzero, Primitives.NotRule.apply⟩

private abbrev requestedWriteRule :
    Contracts.Cycle.Certification.Layer.RuleOccurrence body childContracts :=
  ⟨.requestedWrite, Primitives.AndRule.apply⟩

private abbrev enabledWriteRule :
    Contracts.Cycle.Certification.Layer.RuleOccurrence body childContracts :=
  ⟨.enabledWrite, Primitives.AndRule.apply⟩

private abbrev rs1MuxRule :
    Contracts.Cycle.Certification.Layer.RuleOccurrence body childContracts :=
  ⟨.rs1Mux, Modules.Mux.Rule.select⟩

private abbrev rs2MuxRule :
    Contracts.Cycle.Certification.Layer.RuleOccurrence body childContracts :=
  ⟨.rs2Mux, Modules.Mux.Rule.select⟩


private def scheduleOrders :
    ScheduleDerivation.RuleScheduleOrders body childContracts cycleContract where
  output
    | .cpuregs_rs1 => [zeroAddressRule, zeroWordRule, rs1ZeroRule,
        bankRead 0, rs1MuxRule]
    | .cpuregs_rs2 => [zeroAddressRule, zeroWordRule, rs2ZeroRule,
        bankRead 1, rs2MuxRule]
  state := [zeroAddressRule, rdZeroRule, rdNonzeroRule,
    requestedWriteRule, enabledWriteRule]

private def derivedRuleSchedules :
    ScheduleDerivation.DerivedRuleSchedules body childContracts cycleContract := by
  derive_rule_schedules scheduleOrders

private abbrev ruleSchedules := derivedRuleSchedules.schedules

private theorem coversChildren : ruleSchedules.CoversChildren :=
  derivedRuleSchedules.coversChildren

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

noncomputable opaque certifiedLayer :
    Contracts.Cycle.ModuleCycleCertifiedLayer body childContracts cycleContract :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    ruleSchedules coversChildren stateCorresponds hasCorrespondingState implements

@[reducible] private noncomputable def certifiedChildren :
    Contracts.Cycle.Certification.Layer.ChildStructures body childContracts
  | .bank => (Modules.RegisterBank.certified wordType 5 2).certifiedStructure
  | .zeroAddress => (Modules.Constant.certified addressType zeroAddressValue).certifiedStructure
  | .zeroWord => (Modules.Constant.certified wordType zeroWordValue).certifiedStructure
  | .rs1Zero | .rs2Zero | .rdZero =>
      (Modules.Equality.certified addressType).certifiedStructure
  | .rdNonzero => Primitives.notCertified.certifiedStructure
  | .requestedWrite | .enabledWrite => Primitives.andCertified.certifiedStructure
  | .rs1Mux | .rs2Mux => (Modules.Mux.certified wordType).certifiedStructure

noncomputable opaque certification :
    Contracts.Cycle.ModuleCycleCertification moduleStructure cycleContract :=
  certifiedLayer.certifyComposite structuralChildren certifiedChildren (by
    intro child
    cases child <;> rfl)

/-- The concrete register-file hierarchy certified against the PicoRV32 cycle contract. -/
noncomputable def certified : Contracts.Cycle.ModuleCycleCertified ports :=
  certification.bundle

@[simp] theorem certified_moduleStructure :
    certified.moduleStructure = moduleStructure := rfl

@[simp] theorem certified_cycleContract :
    certified.cycleContract = cycleContract := rfl

/-- The register-file hierarchy and every module below it have concrete structure. -/
theorem hasExactlyOneSolution (inputs : ports.inputs.Values)
    (currentState : moduleStructure.State) :
    ∃ proposal, moduleStructure.IsSolution inputs currentState proposal ∧
      ∀ other, moduleStructure.IsSolution inputs currentState other → other = proposal :=
  certified.hasExactlyOneStructuralResult inputs currentState

end Silean.Examples.PicoRV.Regs

namespace Silean.Examples.PicoRV.Regs.Naming

open Silean Silean.Naming

/-- Original PicoRV32 register-file signal names at the module boundary. -/
def ports : ModulePortsNaming Regs.ports where
  inputs := ⟨fun
    | .resetn => "resetn"
    | .decoded_rs1 => "decoded_rs1"
    | .decoded_rs2 => "decoded_rs2"
    | .cpuregs_write => "cpuregs_write"
    | .latched_rd => "latched_rd"
    | .cpuregs_wrdata => "cpuregs_wrdata"⟩
  outputs := ⟨fun
    | .cpuregs_rs1 => "cpuregs_rs1"
    | .cpuregs_rs2 => "cpuregs_rs2"⟩

def naming : ModuleNaming Regs.moduleStructure := by
  unfold Regs.moduleStructure
  exact .composite ⟨"picorv32_regs", "structural", []⟩ ports
    (fun
      | .bank => "cpuregs"
      | .zeroAddress => "zero_address"
      | .zeroWord => "zero_word"
      | .rs1Zero => "rs1_zero"
      | .rs2Zero => "rs2_zero"
      | .rdZero => "rd_zero"
      | .rdNonzero => "rd_nonzero"
      | .requestedWrite => "requested_write"
      | .enabledWrite => "enabled_write"
      | .rs1Mux => "rs1_mux"
      | .rs2Mux => "rs2_mux")
    (fun
      | .bank => Modules.RegisterBank.Naming.naming (.vector 32 .bit) 5 2
      | .zeroAddress => Modules.Constant.Naming.naming (.vector 5 .bit) (fun _ => false)
      | .zeroWord => Modules.Constant.Naming.naming (.vector 32 .bit) (fun _ => false)
      | .rs1Zero | .rs2Zero | .rdZero => Modules.Equality.Naming.naming (.vector 5 .bit)
      | .rdNonzero => Silean.Naming.Primitive.not
      | .requestedWrite | .enabledWrite => Silean.Naming.Primitive.and
      | .rs1Mux | .rs2Mux => Modules.Mux.Naming.naming (.vector 32 .bit))

def namedModule : NamedModule where
  ports := Regs.ports
  moduleStructure := Regs.moduleStructure
  naming := naming

end Silean.Examples.PicoRV.Regs.Naming
