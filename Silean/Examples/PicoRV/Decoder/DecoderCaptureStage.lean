import Silean.Examples.PicoRV.Decoder.DecoderTypes
import Silean.Contracts.Cycle.CycleContract
import Silean.Contracts.Cycle.CycleEvaluation
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Modules.VectorSlice
import Silean.Modules.EqualsConstant
import Silean.Modules.EnabledRegister
import Silean.Modules.EnabledResetRegister
import Silean.Modules.Constant
import Silean.Naming.SignalAdapterNaming
import Silean.Naming.PrimitiveNaming

namespace Silean.Examples.PicoRV.Decoder.CaptureStage

open Silean
open Silean.Examples.PicoRV.Decoder
open Contracts.Cycle.Certification.Layer

/-! The first registered decoder stage. It captures broad opcode classes,
register addresses, and the J immediate when an instruction read completes.
Only the branch-class register is reset in the selected PicoRV32 source. -/

inductive Input
  | resetn
  | mem_do_rinst
  | mem_done
  | mem_rdata_latched
deriving Enumeration

inductive Register
  | instr_lui | instr_auipc | instr_jal | instr_jalr
  | decoded_rd | decoded_rs1 | decoded_rs2 | decoded_imm_j
  | compressed_instr
  | is_beq_bne_blt_bge_bltu_bgeu
  | is_lb_lh_lw_lbu_lhu
  | is_sb_sh_sw
  | is_alu_reg_imm
  | is_alu_reg_reg
deriving Enumeration

@[reducible] def inputMap : SignalMap :=
  EnumeratedMap.of Input fun
    | .mem_rdata_latched => .vector 32 .bit
    | _ => .bit

def registerType : Register → SignalType
  | .decoded_rd | .decoded_rs1 | .decoded_rs2 => .vector 5 .bit
  | .decoded_imm_j => .vector 32 .bit
  | _ => .bit

@[reducible] def stateMap : SignalMap := EnumeratedMap.of Register registerType

@[reducible] def ports : ModulePorts := ⟨inputMap, stateMap⟩

structure Inputs where
  resetn : Bool
  mem_do_rinst : Bool
  mem_done : Bool
  mem_rdata_latched : Word

private def bits (width value : Nat) : Fin width → Bool :=
  fun index => value.testBit index.val

def valuesOf (inputs : inputMap.Values) : Inputs where
  resetn := inputs .resetn
  mem_do_rinst := inputs .mem_do_rinst
  mem_done := inputs .mem_done
  mem_rdata_latched := inputs .mem_rdata_latched

private def opcodeBits (word : Word) : Fin 7 → Bool :=
  Modules.VectorSlice.slice (prefixWidth := 0) (width := 7) (suffixWidth := 25) word

private def funct3Bits (word : Word) : Fin 3 → Bool :=
  Modules.VectorSlice.slice (prefixWidth := 12) (width := 3) (suffixWidth := 17) word

private def addressBits (low : Nat) (suffix : Nat)
    (word : Fin (low + 5 + suffix) → Bool) : RegisterAddress :=
  Modules.VectorSlice.slice (prefixWidth := low) (width := 5) (suffixWidth := suffix) word

private def matchesBits (width value : Nat) (actual : Fin width → Bool) : Bool :=
  (SignalType.vector width .bit).equal actual (bits width value)

private def immediateJBits (word : Word) : Word := fun index =>
  if _zero : index.val = 0 then false
  else if _low : index.val ≤ 10 then word ⟨index.val + 20, by omega⟩
  else if _eleven : index.val = 11 then word ⟨20, by omega⟩
  else if _middle : index.val ≤ 19 then word index
  else word ⟨31, by omega⟩

def captured (inputs : Inputs) (state : stateMap.Values) : stateMap.Values :=
  if !(inputs.mem_do_rinst && inputs.mem_done) then state else
  let word := inputs.mem_rdata_latched
  let state := stateMap.set state .instr_lui (matchesBits 7 0x37 (opcodeBits word))
  let state := stateMap.set state .instr_auipc (matchesBits 7 0x17 (opcodeBits word))
  let state := stateMap.set state .instr_jal (matchesBits 7 0x6f (opcodeBits word))
  let state := stateMap.set state .instr_jalr
    (matchesBits 7 0x67 (opcodeBits word) && matchesBits 3 0 (funct3Bits word))
  let state := stateMap.set state .is_beq_bne_blt_bge_bltu_bgeu
    (matchesBits 7 0x63 (opcodeBits word))
  let state := stateMap.set state .is_lb_lh_lw_lbu_lhu
    (matchesBits 7 0x03 (opcodeBits word))
  let state := stateMap.set state .is_sb_sh_sw (matchesBits 7 0x23 (opcodeBits word))
  let state := stateMap.set state .is_alu_reg_imm (matchesBits 7 0x13 (opcodeBits word))
  let state := stateMap.set state .is_alu_reg_reg (matchesBits 7 0x33 (opcodeBits word))
  let state := stateMap.set state .decoded_rd (addressBits 7 20 word)
  let state := stateMap.set state .decoded_rs1 (addressBits 15 12 word)
  let state := stateMap.set state .decoded_rs2 (addressBits 20 7 word)
  let state := stateMap.set state .decoded_imm_j (immediateJBits word)
  stateMap.set state .compressed_instr false

def nextState (inputs : Inputs) (state : stateMap.Values) : stateMap.Values :=
  let state := captured inputs state
  if inputs.resetn then state else
    stateMap.set state .is_beq_bne_blt_bge_bltu_bgeu false

inductive Rule | outputs
deriving Enumeration

def outputRule : Contracts.Cycle.CycleOutputRule ports stateMap
    { inputTypes := .nil, outputTypes := .ofList stateMap.types } where
  readsInputs := .nil
  writesOutputs := stateMap.allSelection
  target := fun _ state => stateMap.allSelection.project state

def stateRule : Contracts.Cycle.CycleStateRule ports stateMap where
  inputTypes := .cons .bit (.cons .bit (.cons .bit (.cons (.vector 32 .bit) .nil)))
  readsInputs := (((inputMap.select .mem_rdata_latched).prepend .mem_done).prepend
    .mem_do_rinst).prepend .resetn
  target
    | (resetn, (mem_do_rinst, (mem_done, (mem_rdata_latched, ())))), state =>
      nextState ⟨resetn, mem_do_rinst, mem_done, mem_rdata_latched⟩ state

@[simp] theorem outputRule_writes (output : Register) :
    output ∈ outputRule.writesOutputs.labels := by
  rw [show outputRule.writesOutputs = stateMap.allSelection from rfl,
    SignalMap.allSelection_labels]
  exact (stateMap.labels.locate output).mem

@[simp] theorem stateRule_reads (input : Input) :
    input ∈ stateRule.readsInputs.labels := by
  cases input <;> simp [stateRule, SignalSelection.labels,
    SignalSelection.prepend, SignalMap.select]

@[reducible] def cycleContract : Contracts.Cycle.ModuleCycleContract ports where
  state := stateMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .outputs => ⟨_, outputRule⟩
  stateRule := stateRule
  outputCoverage := by
    change stateMap.allSelection.labels.Perm stateMap.labels.values
    rw [SignalMap.allSelection_labels]

@[simp] theorem outputRule_holds_iff
    (inputs : ports.inputs.Values) (state : stateMap.Values)
    (outputs : ports.outputs.Values) :
    outputRule.Holds inputs state outputs ↔ outputs = state := by
  simp [outputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalSelection.allSelection_matches_project_iff]

/-! ## Hardware structure

The source's thirteen non-reset fields share one aggregate enabled register.
The branch-class flag uses a separate enabled/reset register because the final
reset block overrides only that assignment. -/

def storedFields : SignalTypes :=
  .cons .bit (.cons .bit (.cons .bit (.cons .bit
    (.cons (.vector 5 .bit) (.cons (.vector 5 .bit) (.cons (.vector 5 .bit)
    (.cons (.vector 32 .bit) (.cons .bit (.cons .bit (.cons .bit
    (.cons .bit (.cons .bit .nil))))))))))))

def storedType : SignalType := .tuple storedFields

private abbrev pInstrLui : storedFields.Position := .head
private abbrev pInstrAuipc : storedFields.Position := .tail .head
private abbrev pInstrJal : storedFields.Position := .tail (.tail .head)
private abbrev pInstrJalr : storedFields.Position := .tail (.tail (.tail .head))
private abbrev pDecodedRd : storedFields.Position := .tail (.tail (.tail (.tail .head)))
private abbrev pDecodedRs1 : storedFields.Position :=
  .tail (.tail (.tail (.tail (.tail .head))))
private abbrev pDecodedRs2 : storedFields.Position :=
  .tail (.tail (.tail (.tail (.tail (.tail .head)))))
private abbrev pDecodedImmJ : storedFields.Position :=
  .tail (.tail (.tail (.tail (.tail (.tail (.tail .head))))))
private abbrev pCompressed : storedFields.Position :=
  .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail .head)))))))
private abbrev pLoad : storedFields.Position :=
  .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail .head))))))))
private abbrev pStore : storedFields.Position :=
  .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail .head)))))))))
private abbrev pAluImm : storedFields.Position :=
  .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail .head))))))))))
private abbrev pAluReg : storedFields.Position :=
  .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail .head)))))))))))

private def wordSplitter : Composition.SignalSplitter := .vector 32 .bit
private def immediateCombiner : Composition.SignalCombiner := .vector 32 .bit
private def storedCombiner : Composition.SignalCombiner := .tuple storedFields
private def storedSplitter : Composition.SignalSplitter := .tuple storedFields

inductive Instance
  | captureEnable
  | reset
  | opcode
  | funct3
  | decodedRd
  | decodedRs1
  | decodedRs2
  | opcodeLui
  | opcodeAuipc
  | opcodeJal
  | opcodeJalr
  | opcodeBranch
  | opcodeLoad
  | opcodeStore
  | opcodeAluImm
  | opcodeAluReg
  | funct3Zero
  | jalr
  | zero
  | wordBits
  | immediate
  | storedNext
  | stored
  | storedOutputs
  | branch
deriving Enumeration, DecidableEq

@[reducible] def instancePorts : InstancePorts := EnumeratedMap.of Instance fun
  | .captureEnable | .jalr => Primitives.and.ports
  | .reset => Primitives.not.ports
  | .opcode => Modules.VectorSlice.ports .bit 0 7 25
  | .funct3 => Modules.VectorSlice.ports .bit 12 3 17
  | .decodedRd => Modules.VectorSlice.ports .bit 7 5 20
  | .decodedRs1 => Modules.VectorSlice.ports .bit 15 5 12
  | .decodedRs2 => Modules.VectorSlice.ports .bit 20 5 7
  | .opcodeLui | .opcodeAuipc | .opcodeJal | .opcodeJalr |
      .opcodeBranch | .opcodeLoad | .opcodeStore | .opcodeAluImm | .opcodeAluReg =>
      Modules.EqualsConstant.ports (.vector 7 .bit)
  | .funct3Zero => Modules.EqualsConstant.ports (.vector 3 .bit)
  | .zero => Modules.Constant.ports .bit
  | .wordBits => wordSplitter.ports
  | .immediate => immediateCombiner.ports
  | .storedNext => storedCombiner.ports
  | .stored => Modules.EnabledRegister.ports storedType
  | .storedOutputs => storedSplitter.ports
  | .branch => Modules.EnabledResetRegister.ports .bit

@[reducible] def context : EndpointContext where
  ports := ports
  instancePorts := instancePorts

private def immediateSource (index : Fin 32) :
    SignalSource context.ports context.instancePorts .bit :=
  if zero : index.val = 0 then context.instanceOutput .zero .output
  else if low : index.val ≤ 10 then
    context.instanceOutput .wordBits
      ⟨index.val + 20, by omega⟩
  else if eleven : index.val = 11 then
    context.instanceOutput .wordBits ⟨20, by omega⟩
  else if middle : index.val ≤ 19 then
    context.instanceOutput .wordBits index
  else
    context.instanceOutput .wordBits ⟨31, by omega⟩

def wiring : Wiring context.ports context.instancePorts where
  moduleOutput
    | .is_beq_bne_blt_bge_bltu_bgeu => context.instanceOutput .branch .value
    | .instr_lui => context.instanceOutput .storedOutputs pInstrLui
    | .instr_auipc => context.instanceOutput .storedOutputs pInstrAuipc
    | .instr_jal => context.instanceOutput .storedOutputs pInstrJal
    | .instr_jalr => context.instanceOutput .storedOutputs pInstrJalr
    | .decoded_rd => context.instanceOutput .storedOutputs pDecodedRd
    | .decoded_rs1 => context.instanceOutput .storedOutputs pDecodedRs1
    | .decoded_rs2 => context.instanceOutput .storedOutputs pDecodedRs2
    | .decoded_imm_j => context.instanceOutput .storedOutputs pDecodedImmJ
    | .compressed_instr => context.instanceOutput .storedOutputs pCompressed
    | .is_lb_lh_lw_lbu_lhu => context.instanceOutput .storedOutputs pLoad
    | .is_sb_sh_sw => context.instanceOutput .storedOutputs pStore
    | .is_alu_reg_imm => context.instanceOutput .storedOutputs pAluImm
    | .is_alu_reg_reg => context.instanceOutput .storedOutputs pAluReg
  instanceInput
    | .captureEnable, .left => context.moduleInput .mem_do_rinst
    | .captureEnable, .right => context.moduleInput .mem_done
    | .reset, .input => context.moduleInput .resetn
    | .opcode, .value | .funct3, .value | .decodedRd, .value |
        .decodedRs1, .value | .decodedRs2, .value | .wordBits, .value =>
        context.moduleInput .mem_rdata_latched
    | .opcodeLui, .value | .opcodeAuipc, .value | .opcodeJal, .value |
        .opcodeJalr, .value | .opcodeBranch, .value | .opcodeLoad, .value |
        .opcodeStore, .value | .opcodeAluImm, .value | .opcodeAluReg, .value =>
        context.instanceOutput .opcode .result
    | .funct3Zero, .value => context.instanceOutput .funct3 .result
    | .jalr, .left => context.instanceOutput .opcodeJalr .result
    | .jalr, .right => context.instanceOutput .funct3Zero .result
    | .zero, impossible => nomatch impossible
    | .immediate, index => immediateSource index
    | .storedNext, position =>
        match position with
        | .head => context.instanceOutput .opcodeLui .result
        | .tail .head => context.instanceOutput .opcodeAuipc .result
        | .tail (.tail .head) => context.instanceOutput .opcodeJal .result
        | .tail (.tail (.tail .head)) => context.instanceOutput .jalr .output
        | .tail (.tail (.tail (.tail .head))) => context.instanceOutput .decodedRd .result
        | .tail (.tail (.tail (.tail (.tail .head)))) =>
            context.instanceOutput .decodedRs1 .result
        | .tail (.tail (.tail (.tail (.tail (.tail .head))))) =>
            context.instanceOutput .decodedRs2 .result
        | .tail (.tail (.tail (.tail (.tail (.tail (.tail .head)))))) =>
            context.instanceOutput .immediate .value
        | .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail .head))))))) =>
            context.instanceOutput .zero .output
        | .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail .head)))))))) =>
            context.instanceOutput .opcodeLoad .result
        | .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail .head))))))))) =>
            context.instanceOutput .opcodeStore .result
        | .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail .head)))))))))) =>
            context.instanceOutput .opcodeAluImm .result
        | .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail .head))))))))))) =>
            context.instanceOutput .opcodeAluReg .result
    | .stored, .value => context.instanceOutput .storedNext .value
    | .stored, .enable => context.instanceOutput .captureEnable .output
    | .storedOutputs, .value => context.instanceOutput .stored .value
    | .branch, .value => context.instanceOutput .opcodeBranch .result
    | .branch, .enable => context.instanceOutput .captureEnable .output
    | .branch, .reset => context.instanceOutput .reset .output

@[reducible] def body : ModuleBody := ⟨context, wiring⟩

@[reducible] def childContracts : Contracts.Cycle.ChildCycleContracts body
  | .captureEnable | .jalr => Primitives.andCycleContract
  | .reset => Primitives.notCycleContract
  | .opcode => Modules.VectorSlice.cycleContract .bit 0 7 25
  | .funct3 => Modules.VectorSlice.cycleContract .bit 12 3 17
  | .decodedRd => Modules.VectorSlice.cycleContract .bit 7 5 20
  | .decodedRs1 => Modules.VectorSlice.cycleContract .bit 15 5 12
  | .decodedRs2 => Modules.VectorSlice.cycleContract .bit 20 5 7
  | .opcodeLui => Modules.EqualsConstant.cycleContract (.vector 7 .bit) (bits 7 0x37)
  | .opcodeAuipc => Modules.EqualsConstant.cycleContract (.vector 7 .bit) (bits 7 0x17)
  | .opcodeJal => Modules.EqualsConstant.cycleContract (.vector 7 .bit) (bits 7 0x6f)
  | .opcodeJalr => Modules.EqualsConstant.cycleContract (.vector 7 .bit) (bits 7 0x67)
  | .opcodeBranch => Modules.EqualsConstant.cycleContract (.vector 7 .bit) (bits 7 0x63)
  | .opcodeLoad => Modules.EqualsConstant.cycleContract (.vector 7 .bit) (bits 7 0x03)
  | .opcodeStore => Modules.EqualsConstant.cycleContract (.vector 7 .bit) (bits 7 0x23)
  | .opcodeAluImm => Modules.EqualsConstant.cycleContract (.vector 7 .bit) (bits 7 0x13)
  | .opcodeAluReg => Modules.EqualsConstant.cycleContract (.vector 7 .bit) (bits 7 0x33)
  | .funct3Zero => Modules.EqualsConstant.cycleContract (.vector 3 .bit) (bits 3 0)
  | .zero => Modules.Constant.cycleContract .bit false
  | .wordBits => wordSplitter.cycleContract
  | .immediate => immediateCombiner.cycleContract
  | .storedNext => storedCombiner.cycleContract
  | .stored => Modules.EnabledRegister.cycleContract storedType
  | .storedOutputs => storedSplitter.cycleContract
  | .branch => Modules.EnabledResetRegister.cycleContract .bit false

@[reducible] def structuralChildren :
    (child : Instance) → ModuleStructure (instancePorts.ports child)
  | .captureEnable | .jalr => .primitive Primitives.and
  | .reset => .primitive Primitives.not
  | .opcode => Modules.VectorSlice.moduleStructure .bit 0 7 25
  | .funct3 => Modules.VectorSlice.moduleStructure .bit 12 3 17
  | .decodedRd => Modules.VectorSlice.moduleStructure .bit 7 5 20
  | .decodedRs1 => Modules.VectorSlice.moduleStructure .bit 15 5 12
  | .decodedRs2 => Modules.VectorSlice.moduleStructure .bit 20 5 7
  | .opcodeLui => Modules.EqualsConstant.moduleStructure (.vector 7 .bit) (bits 7 0x37)
  | .opcodeAuipc => Modules.EqualsConstant.moduleStructure (.vector 7 .bit) (bits 7 0x17)
  | .opcodeJal => Modules.EqualsConstant.moduleStructure (.vector 7 .bit) (bits 7 0x6f)
  | .opcodeJalr => Modules.EqualsConstant.moduleStructure (.vector 7 .bit) (bits 7 0x67)
  | .opcodeBranch => Modules.EqualsConstant.moduleStructure (.vector 7 .bit) (bits 7 0x63)
  | .opcodeLoad => Modules.EqualsConstant.moduleStructure (.vector 7 .bit) (bits 7 0x03)
  | .opcodeStore => Modules.EqualsConstant.moduleStructure (.vector 7 .bit) (bits 7 0x23)
  | .opcodeAluImm => Modules.EqualsConstant.moduleStructure (.vector 7 .bit) (bits 7 0x13)
  | .opcodeAluReg => Modules.EqualsConstant.moduleStructure (.vector 7 .bit) (bits 7 0x33)
  | .funct3Zero => Modules.EqualsConstant.moduleStructure (.vector 3 .bit) (bits 3 0)
  | .zero => Modules.Constant.moduleStructure .bit false
  | .wordBits => .splitter wordSplitter
  | .immediate => .combiner immediateCombiner
  | .storedNext => .combiner storedCombiner
  | .stored => Modules.EnabledRegister.moduleStructure storedType
  | .storedOutputs => .splitter storedSplitter
  | .branch => Modules.EnabledResetRegister.moduleStructure .bit false

def moduleStructure : ModuleStructure ports := .composite body structuralChildren

/-! ## Structural schedules -/

private abbrev occurrence (child : Instance)
    (rule : (childContracts child).RuleName) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence body childContracts :=
  ⟨child, rule⟩

private abbrev captureEnableRule := occurrence .captureEnable Primitives.AndRule.apply
private abbrev resetRule := occurrence .reset Primitives.NotRule.apply
private abbrev opcodeRule := occurrence .opcode Modules.VectorSlice.Rule.apply
private abbrev funct3Rule := occurrence .funct3 Modules.VectorSlice.Rule.apply
private abbrev decodedRdRule := occurrence .decodedRd Modules.VectorSlice.Rule.apply
private abbrev decodedRs1Rule := occurrence .decodedRs1 Modules.VectorSlice.Rule.apply
private abbrev decodedRs2Rule := occurrence .decodedRs2 Modules.VectorSlice.Rule.apply
private abbrev opcodeLuiRule := occurrence .opcodeLui Modules.Equality.Rule.apply
private abbrev opcodeAuipcRule := occurrence .opcodeAuipc Modules.Equality.Rule.apply
private abbrev opcodeJalRule := occurrence .opcodeJal Modules.Equality.Rule.apply
private abbrev opcodeJalrRule := occurrence .opcodeJalr Modules.Equality.Rule.apply
private abbrev opcodeBranchRule := occurrence .opcodeBranch Modules.Equality.Rule.apply
private abbrev opcodeLoadRule := occurrence .opcodeLoad Modules.Equality.Rule.apply
private abbrev opcodeStoreRule := occurrence .opcodeStore Modules.Equality.Rule.apply
private abbrev opcodeAluImmRule := occurrence .opcodeAluImm Modules.Equality.Rule.apply
private abbrev opcodeAluRegRule := occurrence .opcodeAluReg Modules.Equality.Rule.apply
private abbrev funct3ZeroRule := occurrence .funct3Zero Modules.Equality.Rule.apply
private abbrev jalrRule := occurrence .jalr Primitives.AndRule.apply
private abbrev zeroRule := occurrence .zero Primitives.ConstantRule.apply
private abbrev wordBitsRule := occurrence .wordBits Composition.SignalComponentRule.apply
private abbrev immediateRule := occurrence .immediate Composition.SignalComponentRule.apply
private abbrev storedNextRule := occurrence .storedNext Composition.SignalComponentRule.apply
private abbrev storedRule := occurrence .stored Modules.EnabledRegister.Rule.observe
private abbrev storedOutputsRule :=
  occurrence .storedOutputs Composition.SignalComponentRule.apply
private abbrev branchRule := occurrence .branch Modules.EnabledResetRegister.Rule.observe


private def scheduleOrders :
    ScheduleDerivation.RuleScheduleOrders body childContracts cycleContract where
  output := fun | .outputs => [storedRule, storedOutputsRule, branchRule]
  state := [captureEnableRule, resetRule, opcodeRule, funct3Rule,
    decodedRdRule, decodedRs1Rule, decodedRs2Rule, wordBitsRule, zeroRule,
    opcodeLuiRule, opcodeAuipcRule, opcodeJalRule, opcodeJalrRule,
    opcodeBranchRule, opcodeLoadRule, opcodeStoreRule, opcodeAluImmRule,
    opcodeAluRegRule, funct3ZeroRule, jalrRule, immediateRule, storedNextRule]

private def derivedRuleSchedules :
    ScheduleDerivation.DerivedRuleSchedules body childContracts cycleContract := by
  derive_rule_schedules scheduleOrders

private abbrev ruleSchedules := derivedRuleSchedules.schedules

private theorem coversChildren : ruleSchedules.CoversChildren :=
  derivedRuleSchedules.coversChildren

/-! ## Cycle certification -/

@[reducible] noncomputable def certifiedChildren :
    ChildStructures body childContracts
  | .captureEnable | .jalr => Primitives.andCertified.certifiedStructure
  | .reset => Primitives.notCertified.certifiedStructure
  | .opcode => (Modules.VectorSlice.certified .bit 0 7 25).certifiedStructure
  | .funct3 => (Modules.VectorSlice.certified .bit 12 3 17).certifiedStructure
  | .decodedRd => (Modules.VectorSlice.certified .bit 7 5 20).certifiedStructure
  | .decodedRs1 => (Modules.VectorSlice.certified .bit 15 5 12).certifiedStructure
  | .decodedRs2 => (Modules.VectorSlice.certified .bit 20 5 7).certifiedStructure
  | .opcodeLui => (Modules.EqualsConstant.certified (.vector 7 .bit)
      (bits 7 0x37)).certifiedStructure
  | .opcodeAuipc => (Modules.EqualsConstant.certified (.vector 7 .bit)
      (bits 7 0x17)).certifiedStructure
  | .opcodeJal => (Modules.EqualsConstant.certified (.vector 7 .bit)
      (bits 7 0x6f)).certifiedStructure
  | .opcodeJalr => (Modules.EqualsConstant.certified (.vector 7 .bit)
      (bits 7 0x67)).certifiedStructure
  | .opcodeBranch => (Modules.EqualsConstant.certified (.vector 7 .bit)
      (bits 7 0x63)).certifiedStructure
  | .opcodeLoad => (Modules.EqualsConstant.certified (.vector 7 .bit)
      (bits 7 0x03)).certifiedStructure
  | .opcodeStore => (Modules.EqualsConstant.certified (.vector 7 .bit)
      (bits 7 0x23)).certifiedStructure
  | .opcodeAluImm => (Modules.EqualsConstant.certified (.vector 7 .bit)
      (bits 7 0x13)).certifiedStructure
  | .opcodeAluReg => (Modules.EqualsConstant.certified (.vector 7 .bit)
      (bits 7 0x33)).certifiedStructure
  | .funct3Zero => (Modules.EqualsConstant.certified (.vector 3 .bit)
      (bits 3 0)).certifiedStructure
  | .zero => (Modules.Constant.certified .bit false).certifiedStructure
  | .wordBits => wordSplitter.certified.certifiedStructure
  | .immediate => immediateCombiner.certified.certifiedStructure
  | .storedNext => storedCombiner.certified.certifiedStructure
  | .stored => (Modules.EnabledRegister.certified storedType).certifiedStructure
  | .storedOutputs => storedSplitter.certified.certifiedStructure
  | .branch => (Modules.EnabledResetRegister.certified .bit false).certifiedStructure

private def storedValue (state : stateMap.Values) : storedType.Denote :=
  (state .instr_lui, (state .instr_auipc, (state .instr_jal,
    (state .instr_jalr, (state .decoded_rd, (state .decoded_rs1,
    (state .decoded_rs2, (state .decoded_imm_j, (state .compressed_instr,
    (state .is_lb_lh_lw_lbu_lhu, (state .is_sb_sh_sw,
    (state .is_alu_reg_imm, (state .is_alu_reg_reg, ())))))))))))))

private def captureData (inputs : Inputs) : storedType.Denote :=
  let word := inputs.mem_rdata_latched
  (matchesBits 7 0x37 (opcodeBits word),
    (matchesBits 7 0x17 (opcodeBits word),
    (matchesBits 7 0x6f (opcodeBits word),
    (matchesBits 7 0x67 (opcodeBits word) && matchesBits 3 0 (funct3Bits word),
    (addressBits 7 20 word, (addressBits 15 12 word, (addressBits 20 7 word,
    (immediateJBits word, (false, (matchesBits 7 0x03 (opcodeBits word),
    (matchesBits 7 0x23 (opcodeBits word),
    (matchesBits 7 0x13 (opcodeBits word),
    (matchesBits 7 0x33 (opcodeBits word), ())))))))))))))

private theorem storedValue_captured (inputs : Inputs) (state : stateMap.Values) :
    storedValue (captured inputs state) =
      bif (inputs.mem_do_rinst && inputs.mem_done)
        then captureData inputs else storedValue state := by
  rcases inputs with ⟨resetn, memDoRinst, memDone, word⟩
  cases memDoRinst <;> cases memDone <;>
    simp [captured, storedValue, captureData, SignalMap.set]

private theorem branch_nextState (inputs : Inputs) (state : stateMap.Values) :
    nextState inputs state .is_beq_bne_blt_bge_bltu_bgeu =
      bif !inputs.resetn then false
      else bif (inputs.mem_do_rinst && inputs.mem_done)
        then matchesBits 7 0x63 (opcodeBits inputs.mem_rdata_latched)
        else state .is_beq_bne_blt_bge_bltu_bgeu := by
  rcases inputs with ⟨resetn, memDoRinst, memDone, word⟩
  cases resetn <;> cases memDoRinst <;> cases memDone <;>
    simp [nextState, captured, SignalMap.set]

private theorem storedValue_nextState (inputs : Inputs) (state : stateMap.Values) :
    storedValue (nextState inputs state) = storedValue (captured inputs state) := by
  rcases inputs with ⟨resetn, memDoRinst, memDone, word⟩
  cases resetn <;> simp [nextState, storedValue, SignalMap.set]

private def storedContractState (state : stateMap.Values) :
    (Modules.EnabledRegister.cycleContract storedType).state.Values :=
  fun | .stored => storedValue state

private def branchContractState (state : stateMap.Values) :
    (Modules.EnabledResetRegister.cycleContract .bit false).state.Values :=
  fun | .stored => state .is_beq_bne_blt_bge_bltu_bgeu

private def mergeStoredState (stored : storedType.Denote) (branch : Bool) :
    stateMap.Values := fun
  | .instr_lui => stored.1
  | .instr_auipc => stored.2.1
  | .instr_jal => stored.2.2.1
  | .instr_jalr => stored.2.2.2.1
  | .decoded_rd => stored.2.2.2.2.1
  | .decoded_rs1 => stored.2.2.2.2.2.1
  | .decoded_rs2 => stored.2.2.2.2.2.2.1
  | .decoded_imm_j => stored.2.2.2.2.2.2.2.1
  | .compressed_instr => stored.2.2.2.2.2.2.2.2.1
  | .is_beq_bne_blt_bge_bltu_bgeu => branch
  | .is_lb_lh_lw_lbu_lhu => stored.2.2.2.2.2.2.2.2.2.1
  | .is_sb_sh_sw => stored.2.2.2.2.2.2.2.2.2.2.1
  | .is_alu_reg_imm => stored.2.2.2.2.2.2.2.2.2.2.2.1
  | .is_alu_reg_reg => stored.2.2.2.2.2.2.2.2.2.2.2.2.1

@[simp] private theorem storedValue_mergeStoredState (stored : storedType.Denote)
    (branch : Bool) : storedValue (mergeStoredState stored branch) = stored := by
  rcases stored with ⟨a, b, c, d, rd, rs1, rs2, immediate, compressed,
    load, store, aluImm, aluReg, tail⟩
  cases tail
  rfl

section Certification

variable (layerChildren : ChildStructures body childContracts)

private abbrev certificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren

private def stateCorresponds (contractState : stateMap.Values)
    (structuralState : (certificationStructure layerChildren).State) : Prop :=
  (layerChildren .stored).certification.stateCorresponds
      (storedContractState contractState) (structuralState .stored) ∧
    (layerChildren .branch).certification.stateCorresponds
      (branchContractState contractState) (structuralState .branch)

private theorem hasCorrespondingState
    (structuralState : (certificationStructure layerChildren).State) :
    ∃ contractState, stateCorresponds layerChildren contractState structuralState := by
  rcases (layerChildren .stored).certification.hasCorrespondingState
      (structuralState .stored) with ⟨stored, storedCorresponds⟩
  rcases (layerChildren .branch).certification.hasCorrespondingState
      (structuralState .branch) with ⟨branch, branchCorresponds⟩
  let merged := mergeStoredState (stored .stored) (branch .stored)
  refine ⟨merged, ?_, ?_⟩
  · have equal : storedContractState merged = stored := by
      funext name
      cases name
      simp [storedContractState, merged]
    rw [equal]
    exact storedCorresponds
  · have equal : branchContractState merged = branch := by
      funext name
      cases name
      simp [branchContractState, merged, mergeStoredState]
    rw [equal]
    exact branchCorresponds

private theorem implements :
    Contracts.Cycle.Implements (certificationStructure layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have childEvaluation (child : Instance) : ∃ state,
      (childContracts child).EvaluatesTo
        (ProposedValues.childInputs body
          (fun name => (layerChildren name).moduleStructure) inputs proposal.2 child)
        state (proposal.2 child).outputs
        ((childContracts child).stateRule.apply
          (ProposedValues.childInputs body
            (fun name => (layerChildren name).moduleStructure) inputs proposal.2 child)
          state) := by
    rcases (layerChildren child).certification.hasCorrespondingState
        (structuralState child) with ⟨state, stateCorresponds⟩
    exact ⟨state, (childSolutionMatchesContract layerChildren inputs structuralState
      proposal satisfies child state stateCorresponds).1⟩
  have captureEnableEval := (childEvaluation .captureEnable).choose_spec
  have resetEval := (childEvaluation .reset).choose_spec
  have opcodeEval := (childEvaluation .opcode).choose_spec
  have funct3Eval := (childEvaluation .funct3).choose_spec
  have decodedRdEval := (childEvaluation .decodedRd).choose_spec
  have decodedRs1Eval := (childEvaluation .decodedRs1).choose_spec
  have decodedRs2Eval := (childEvaluation .decodedRs2).choose_spec
  have opcodeLuiEval := (childEvaluation .opcodeLui).choose_spec
  have opcodeAuipcEval := (childEvaluation .opcodeAuipc).choose_spec
  have opcodeJalEval := (childEvaluation .opcodeJal).choose_spec
  have opcodeJalrEval := (childEvaluation .opcodeJalr).choose_spec
  have opcodeBranchEval := (childEvaluation .opcodeBranch).choose_spec
  have opcodeLoadEval := (childEvaluation .opcodeLoad).choose_spec
  have opcodeStoreEval := (childEvaluation .opcodeStore).choose_spec
  have opcodeAluImmEval := (childEvaluation .opcodeAluImm).choose_spec
  have opcodeAluRegEval := (childEvaluation .opcodeAluReg).choose_spec
  have funct3ZeroEval := (childEvaluation .funct3Zero).choose_spec
  have jalrEval := (childEvaluation .jalr).choose_spec
  have zeroEval := (childEvaluation .zero).choose_spec
  have wordBitsEval := (childEvaluation .wordBits).choose_spec
  have immediateEval := (childEvaluation .immediate).choose_spec
  have storedNextEval := (childEvaluation .storedNext).choose_spec
  have storedOutputsEval := (childEvaluation .storedOutputs).choose_spec
  have storedMatch := childSolutionMatchesContract layerChildren inputs structuralState
    proposal satisfies .stored (storedContractState contractState) corresponds.1
  have branchMatch := childSolutionMatchesContract layerChildren inputs structuralState
    proposal satisfies .branch (branchContractState contractState) corresponds.2

  have captureEnableValue : (proposal.2 .captureEnable).outputs .output =
      (inputs .mem_do_rinst && inputs .mem_done) := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      (captureEnableEval.1 Primitives.AndRule.apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, SignalSource.value] using equation
  have resetValue : (proposal.2 .reset).outputs .output = !inputs .resetn := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      (resetEval.1 Primitives.NotRule.apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, SignalSource.value] using equation
  have opcodeValue : (proposal.2 .opcode).outputs .result =
      opcodeBits (inputs .mem_rdata_latched) := by
    have equation := (Modules.VectorSlice.outputRule_holds_iff .bit 0 7 25 _ _ _).mp
      (opcodeEval.1 Modules.VectorSlice.Rule.apply)
    change (proposal.2 .opcode).outputs .result =
      Modules.VectorSlice.slice (prefixWidth := 0) (width := 7) (suffixWidth := 25)
        (inputs .mem_rdata_latched)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, SignalSource.value] using equation
  have funct3Value : (proposal.2 .funct3).outputs .result =
      funct3Bits (inputs .mem_rdata_latched) := by
    have equation := (Modules.VectorSlice.outputRule_holds_iff .bit 12 3 17 _ _ _).mp
      (funct3Eval.1 Modules.VectorSlice.Rule.apply)
    change (proposal.2 .funct3).outputs .result =
      Modules.VectorSlice.slice (prefixWidth := 12) (width := 3) (suffixWidth := 17)
        (inputs .mem_rdata_latched)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, SignalSource.value] using equation
  have decodedRdValue : (proposal.2 .decodedRd).outputs .result =
      addressBits 7 20 (inputs .mem_rdata_latched) := by
    have equation := (Modules.VectorSlice.outputRule_holds_iff .bit 7 5 20 _ _ _).mp
      (decodedRdEval.1 Modules.VectorSlice.Rule.apply)
    change (proposal.2 .decodedRd).outputs .result =
      Modules.VectorSlice.slice (prefixWidth := 7) (width := 5) (suffixWidth := 20)
        (inputs .mem_rdata_latched)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, SignalSource.value] using equation
  have decodedRs1Value : (proposal.2 .decodedRs1).outputs .result =
      addressBits 15 12 (inputs .mem_rdata_latched) := by
    have equation := (Modules.VectorSlice.outputRule_holds_iff .bit 15 5 12 _ _ _).mp
      (decodedRs1Eval.1 Modules.VectorSlice.Rule.apply)
    change (proposal.2 .decodedRs1).outputs .result =
      Modules.VectorSlice.slice (prefixWidth := 15) (width := 5) (suffixWidth := 12)
        (inputs .mem_rdata_latched)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, SignalSource.value] using equation
  have decodedRs2Value : (proposal.2 .decodedRs2).outputs .result =
      addressBits 20 7 (inputs .mem_rdata_latched) := by
    have equation := (Modules.VectorSlice.outputRule_holds_iff .bit 20 5 7 _ _ _).mp
      (decodedRs2Eval.1 Modules.VectorSlice.Rule.apply)
    change (proposal.2 .decodedRs2).outputs .result =
      Modules.VectorSlice.slice (prefixWidth := 20) (width := 5) (suffixWidth := 7)
        (inputs .mem_rdata_latched)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, SignalSource.value] using equation
  have opcodeLuiValue : (proposal.2 .opcodeLui).outputs .result =
      matchesBits 7 0x37 (opcodeBits (inputs .mem_rdata_latched)) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (bits 7 0x37) _ _ _).mp
        (opcodeLuiEval.1 Modules.Equality.Rule.apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.instanceOutput, SignalSource.value, opcodeValue, matchesBits] using equation
  have opcodeAuipcValue : (proposal.2 .opcodeAuipc).outputs .result =
      matchesBits 7 0x17 (opcodeBits (inputs .mem_rdata_latched)) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (bits 7 0x17) _ _ _).mp
        (opcodeAuipcEval.1 Modules.Equality.Rule.apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.instanceOutput, SignalSource.value, opcodeValue, matchesBits] using equation
  have opcodeJalValue : (proposal.2 .opcodeJal).outputs .result =
      matchesBits 7 0x6f (opcodeBits (inputs .mem_rdata_latched)) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (bits 7 0x6f) _ _ _).mp
        (opcodeJalEval.1 Modules.Equality.Rule.apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.instanceOutput, SignalSource.value, opcodeValue, matchesBits] using equation
  have opcodeJalrValue : (proposal.2 .opcodeJalr).outputs .result =
      matchesBits 7 0x67 (opcodeBits (inputs .mem_rdata_latched)) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (bits 7 0x67) _ _ _).mp
        (opcodeJalrEval.1 Modules.Equality.Rule.apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.instanceOutput, SignalSource.value, opcodeValue, matchesBits] using equation
  have opcodeBranchValue : (proposal.2 .opcodeBranch).outputs .result =
      matchesBits 7 0x63 (opcodeBits (inputs .mem_rdata_latched)) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (bits 7 0x63) _ _ _).mp
        (opcodeBranchEval.1 Modules.Equality.Rule.apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.instanceOutput, SignalSource.value, opcodeValue, matchesBits] using equation
  have opcodeLoadValue : (proposal.2 .opcodeLoad).outputs .result =
      matchesBits 7 0x03 (opcodeBits (inputs .mem_rdata_latched)) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (bits 7 0x03) _ _ _).mp
        (opcodeLoadEval.1 Modules.Equality.Rule.apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.instanceOutput, SignalSource.value, opcodeValue, matchesBits] using equation
  have opcodeStoreValue : (proposal.2 .opcodeStore).outputs .result =
      matchesBits 7 0x23 (opcodeBits (inputs .mem_rdata_latched)) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (bits 7 0x23) _ _ _).mp
        (opcodeStoreEval.1 Modules.Equality.Rule.apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.instanceOutput, SignalSource.value, opcodeValue, matchesBits] using equation
  have opcodeAluImmValue : (proposal.2 .opcodeAluImm).outputs .result =
      matchesBits 7 0x13 (opcodeBits (inputs .mem_rdata_latched)) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (bits 7 0x13) _ _ _).mp
        (opcodeAluImmEval.1 Modules.Equality.Rule.apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.instanceOutput, SignalSource.value, opcodeValue, matchesBits] using equation
  have opcodeAluRegValue : (proposal.2 .opcodeAluReg).outputs .result =
      matchesBits 7 0x33 (opcodeBits (inputs .mem_rdata_latched)) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 7 .bit) (bits 7 0x33) _ _ _).mp
        (opcodeAluRegEval.1 Modules.Equality.Rule.apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.instanceOutput, SignalSource.value, opcodeValue, matchesBits] using equation
  have funct3ZeroValue : (proposal.2 .funct3Zero).outputs .result =
      matchesBits 3 0 (funct3Bits (inputs .mem_rdata_latched)) := by
    have equation := (Modules.EqualsConstant.outputRule_holds_iff
      (.vector 3 .bit) (bits 3 0) _ _ _).mp
        (funct3ZeroEval.1 Modules.Equality.Rule.apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.instanceOutput, SignalSource.value, funct3Value, matchesBits] using equation
  have jalrValue : (proposal.2 .jalr).outputs .output =
      (matchesBits 7 0x67 (opcodeBits (inputs .mem_rdata_latched)) &&
        matchesBits 3 0 (funct3Bits (inputs .mem_rdata_latched))) := by
    have equation := (Primitives.andOutputRule_holds_iff _ _ _).mp
      (jalrEval.1 Primitives.AndRule.apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.instanceOutput, SignalSource.value, opcodeJalrValue,
      funct3ZeroValue] using equation
  have zeroValue : (proposal.2 .zero).outputs .output = false := by
    exact Modules.Constant.output_of_evaluatesTo .bit false _ _ _ _ zeroEval
  have wordBitsValue : (proposal.2 .wordBits).outputs =
      wordSplitter.outputValues (fun | .value => inputs .mem_rdata_latched) := by
    have equation := (wordSplitter.outputRule_holds_iff _ _ _).mp
      (wordBitsEval.1 Composition.SignalComponentRule.apply)
    normalize_child_hyp equation unfolding body, wiring, context
    exact equation
  have wordBitValue (index : Fin 32) :
      (proposal.2 .wordBits).outputs index = inputs .mem_rdata_latched index := by
    have equation := congrFun wordBitsValue index
    simpa [wordSplitter, Composition.SignalSplitter.outputValues] using equation
  have immediateValue : (proposal.2 .immediate).outputs .value =
      immediateJBits (inputs .mem_rdata_latched) := by
    have equation := (immediateCombiner.outputRule_holds_iff _ _ _).mp
      (immediateEval.1 Composition.SignalComponentRule.apply)
    have valueEquation := congrFun equation .value
    normalize_child_hyp valueEquation unfolding body, wiring, context
    rw [valueEquation]
    funext index
    by_cases zero : index.val = 0
    · simp [Composition.SignalCombiner.outputValues, immediateCombiner,
        ProposedValues.childInputs_apply, context, immediateSource,
        zero, EndpointContext.instanceOutput, SignalSource.value, zeroValue, immediateJBits]
    · by_cases low : index.val ≤ 10
      · simp [Composition.SignalCombiner.outputValues, immediateCombiner,
          ProposedValues.childInputs_apply, context, immediateSource,
          zero, low, EndpointContext.instanceOutput, SignalSource.value,
          wordBitValue, immediateJBits]
      · by_cases eleven : index.val = 11
        · simp [Composition.SignalCombiner.outputValues, immediateCombiner,
            ProposedValues.childInputs_apply, context, immediateSource,
            eleven, EndpointContext.instanceOutput, SignalSource.value,
            wordBitValue, immediateJBits]
        · by_cases middle : index.val ≤ 19
          · simp [Composition.SignalCombiner.outputValues, immediateCombiner,
              ProposedValues.childInputs_apply, context, immediateSource,
              zero, low, eleven, middle, EndpointContext.instanceOutput,
              SignalSource.value, wordBitValue, immediateJBits]
          · simp [Composition.SignalCombiner.outputValues, immediateCombiner,
              ProposedValues.childInputs_apply, context, immediateSource,
              zero, low, eleven, middle, EndpointContext.instanceOutput,
              SignalSource.value, wordBitValue, immediateJBits]

  have storedNextValue : (proposal.2 .storedNext).outputs .value =
      captureData (valuesOf inputs) := by
    have equation := (storedCombiner.outputRule_holds_iff _ _ _).mp
      (storedNextEval.1 Composition.SignalComponentRule.apply)
    have valueEquation := congrFun equation .value
    normalize_child_hyp valueEquation unfolding body, wiring, context
    rw [valueEquation]
    simp [Composition.SignalCombiner.outputValues, storedCombiner, storedFields,
      SignalTypes.assemble,
      ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.instanceOutput, SignalSource.value, captureData, valuesOf,
      opcodeLuiValue, opcodeAuipcValue, opcodeJalValue, jalrValue,
      decodedRdValue, decodedRs1Value, decodedRs2Value, immediateValue,
      zeroValue, opcodeLoadValue, opcodeStoreValue, opcodeAluImmValue,
      opcodeAluRegValue]
  have storedCurrent : (proposal.2 .stored).outputs .value = storedValue contractState := by
    exact (Modules.EnabledRegister.outputRule_holds_iff storedType _ _ _).mp
      (storedMatch.1.1 Modules.EnabledRegister.Rule.observe)
  have storedOutputsValue : (proposal.2 .storedOutputs).outputs =
      storedSplitter.outputValues (fun | .value => storedValue contractState) := by
    have equation := (storedSplitter.outputRule_holds_iff _ _ _).mp
      (storedOutputsEval.1 Composition.SignalComponentRule.apply)
    have inputsEqual : ProposedValues.childInputs body
        (fun name => (layerChildren name).moduleStructure) inputs proposal.2 .storedOutputs =
        (fun | .value => storedValue contractState) := by
      funext port
      cases port
      change (proposal.2 .stored).outputs .value = storedValue contractState
      exact storedCurrent
    rw [inputsEqual] at equation
    exact equation
  have branchCurrent : (proposal.2 .branch).outputs .value =
      contractState .is_beq_bne_blt_bge_bltu_bgeu := by
    exact (Modules.EnabledResetRegister.outputRule_holds_iff .bit _ _ _).mp
      (branchMatch.1.1 Modules.EnabledResetRegister.Rule.observe)

  have storedOutputValue (position : storedFields.Position) :
      (proposal.2 .storedOutputs).outputs position =
        SignalTypes.get storedFields (storedValue contractState) position := by
    have equation := congrFun storedOutputsValue position
    simpa [storedSplitter, Composition.SignalSplitter.outputValues] using equation
  let nextContractState := nextState (valuesOf inputs) contractState
  refine ⟨nextContractState, ?_, ?_⟩
  · constructor
    · intro rule
      cases rule
      rw [outputRule_holds_iff]
      funext output
      have boundary := satisfies.1 output
      cases output <;>
        simp [body, wiring, context, EndpointContext.instanceOutput,
          SignalSource.value] at boundary ⊢
      all_goals first | exact boundary.trans branchCurrent | exact boundary.trans (storedOutputValue _)
    · rfl
  · constructor
    · have stateEqual : storedContractState nextContractState =
          (Modules.EnabledRegister.stateRule storedType).apply
            (ProposedValues.childInputs body
              (fun name => (layerChildren name).moduleStructure)
              inputs proposal.2 .stored)
            (storedContractState contractState) := by
        funext name
        cases name
        change storedValue (nextState (valuesOf inputs) contractState) =
          bif (proposal.2 .captureEnable).outputs .output
            then (proposal.2 .storedNext).outputs .value
            else storedValue contractState
        rw [captureEnableValue, storedNextValue, storedValue_nextState,
          storedValue_captured]
        cases inputRinst : inputs .mem_do_rinst <;>
          cases inputDone : inputs .mem_done <;>
          simp [valuesOf, inputRinst, inputDone]
      rw [stateEqual]
      exact storedMatch.2
    · have stateEqual : branchContractState nextContractState =
          (Modules.EnabledResetRegister.stateRule .bit false).apply
            (ProposedValues.childInputs body
              (fun name => (layerChildren name).moduleStructure)
              inputs proposal.2 .branch)
            (branchContractState contractState) := by
        funext name
        cases name
        change nextState (valuesOf inputs) contractState
              .is_beq_bne_blt_bge_bltu_bgeu =
          bif (proposal.2 .reset).outputs .output then false
          else bif (proposal.2 .captureEnable).outputs .output
            then (proposal.2 .opcodeBranch).outputs .result
            else contractState .is_beq_bne_blt_bge_bltu_bgeu
        rw [resetValue, captureEnableValue, opcodeBranchValue,
          branch_nextState]
        cases inputResetn : inputs .resetn <;>
          cases inputRinst : inputs .mem_do_rinst <;>
          cases inputDone : inputs .mem_done <;>
          simp [valuesOf, inputResetn, inputRinst, inputDone]
      rw [stateEqual]
      exact branchMatch.2

end Certification

noncomputable opaque certifiedLayer :
    Contracts.Cycle.ModuleCycleCertifiedLayer body childContracts cycleContract :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    ruleSchedules coversChildren stateCorresponds hasCorrespondingState implements

noncomputable opaque certification :
    Contracts.Cycle.ModuleCycleCertification moduleStructure cycleContract :=
  certifiedLayer.certifyComposite structuralChildren certifiedChildren (by
    intro child
    cases child <;> rfl)

/-- The concrete PicoRV32 decoder capture hierarchy certified against its
cycle contract. -/
noncomputable def certified : Contracts.Cycle.ModuleCycleCertified ports :=
  certification.bundle

@[simp] theorem certified_moduleStructure :
    certified.moduleStructure = moduleStructure := rfl

@[simp] theorem certified_cycleContract :
    certified.cycleContract = cycleContract := rfl

theorem hasExactlyOneSolution (inputs : ports.inputs.Values)
    (currentState : moduleStructure.State) :
    ∃ proposal, moduleStructure.IsSolution inputs currentState proposal ∧
      ∀ other, moduleStructure.IsSolution inputs currentState other → other = proposal :=
  certified.hasExactlyOneStructuralResult inputs currentState

end Silean.Examples.PicoRV.Decoder.CaptureStage

namespace Silean.Examples.PicoRV.Decoder.CaptureStage.Naming

open Silean Silean.Naming

def ports : ModulePortsNaming CaptureStage.ports where
  inputs := ⟨fun
    | .resetn => "resetn"
    | .mem_do_rinst => "mem_do_rinst"
    | .mem_done => "mem_done"
    | .mem_rdata_latched => "mem_rdata_latched"⟩
  outputs := ⟨fun
    | .instr_lui => "instr_lui"
    | .instr_auipc => "instr_auipc"
    | .instr_jal => "instr_jal"
    | .instr_jalr => "instr_jalr"
    | .decoded_rd => "decoded_rd"
    | .decoded_rs1 => "decoded_rs1"
    | .decoded_rs2 => "decoded_rs2"
    | .decoded_imm_j => "decoded_imm_j"
    | .compressed_instr => "compressed_instr"
    | .is_beq_bne_blt_bge_bltu_bgeu => "is_beq_bne_blt_bge_bltu_bgeu"
    | .is_lb_lh_lw_lbu_lhu => "is_lb_lh_lw_lbu_lhu"
    | .is_sb_sh_sw => "is_sb_sh_sw"
    | .is_alu_reg_imm => "is_alu_reg_imm"
    | .is_alu_reg_reg => "is_alu_reg_reg"⟩

private def storedType : SignalTypeNaming CaptureStage.storedType :=
  .tuple (.cons "instr_lui" .bit
    (.cons "instr_auipc" .bit
    (.cons "instr_jal" .bit
    (.cons "instr_jalr" .bit
    (.cons "decoded_rd" (.vector .bit)
    (.cons "decoded_rs1" (.vector .bit)
    (.cons "decoded_rs2" (.vector .bit)
    (.cons "decoded_imm_j" (.vector .bit)
    (.cons "compressed_instr" .bit
    (.cons "is_lb_lh_lw_lbu_lhu" .bit
    (.cons "is_sb_sh_sw" .bit
    (.cons "is_alu_reg_imm" .bit
    (.cons "is_alu_reg_reg" .bit .nil)))))))))))))

def naming : ModuleNaming CaptureStage.moduleStructure := by
  unfold CaptureStage.moduleStructure
  exact .composite ⟨"picorv32_decoder_capture", "structural", []⟩ ports
    (fun
      | .captureEnable => "capture_enable"
      | .reset => "reset"
      | .opcode => "opcode"
      | .funct3 => "funct3"
      | .decodedRd => "slice_decoded_rd"
      | .decodedRs1 => "slice_decoded_rs1"
      | .decodedRs2 => "slice_decoded_rs2"
      | .opcodeLui => "opcode_lui"
      | .opcodeAuipc => "opcode_auipc"
      | .opcodeJal => "opcode_jal"
      | .opcodeJalr => "opcode_jalr"
      | .opcodeBranch => "opcode_branch"
      | .opcodeLoad => "opcode_load"
      | .opcodeStore => "opcode_store"
      | .opcodeAluImm => "opcode_alu_imm"
      | .opcodeAluReg => "opcode_alu_reg"
      | .funct3Zero => "funct3_zero"
      | .jalr => "jalr"
      | .zero => "zero"
      | .wordBits => "word_bits"
      | .immediate => "build_immediate_j"
      | .storedNext => "stored_next"
      | .stored => "stored"
      | .storedOutputs => "stored_outputs"
      | .branch => "branch")
    (fun
      | .captureEnable | .jalr => Primitive.and
      | .reset => Primitive.not
      | .opcode => Modules.VectorSlice.Naming.naming .bit 0 7 25
      | .funct3 => Modules.VectorSlice.Naming.naming .bit 12 3 17
      | .decodedRd => Modules.VectorSlice.Naming.naming .bit 7 5 20
      | .decodedRs1 => Modules.VectorSlice.Naming.naming .bit 15 5 12
      | .decodedRs2 => Modules.VectorSlice.Naming.naming .bit 20 5 7
      | .opcodeLui => Modules.EqualsConstant.Naming.naming (.vector 7 .bit) (CaptureStage.bits 7 0x37)
      | .opcodeAuipc => Modules.EqualsConstant.Naming.naming (.vector 7 .bit) (CaptureStage.bits 7 0x17)
      | .opcodeJal => Modules.EqualsConstant.Naming.naming (.vector 7 .bit) (CaptureStage.bits 7 0x6f)
      | .opcodeJalr => Modules.EqualsConstant.Naming.naming (.vector 7 .bit) (CaptureStage.bits 7 0x67)
      | .opcodeBranch => Modules.EqualsConstant.Naming.naming (.vector 7 .bit) (CaptureStage.bits 7 0x63)
      | .opcodeLoad => Modules.EqualsConstant.Naming.naming (.vector 7 .bit) (CaptureStage.bits 7 0x03)
      | .opcodeStore => Modules.EqualsConstant.Naming.naming (.vector 7 .bit) (CaptureStage.bits 7 0x23)
      | .opcodeAluImm => Modules.EqualsConstant.Naming.naming (.vector 7 .bit) (CaptureStage.bits 7 0x13)
      | .opcodeAluReg => Modules.EqualsConstant.Naming.naming (.vector 7 .bit) (CaptureStage.bits 7 0x33)
      | .funct3Zero => Modules.EqualsConstant.Naming.naming (.vector 3 .bit) (CaptureStage.bits 3 0)
      | .zero => Modules.Constant.Naming.naming .bit false
      | .wordBits => SignalAdapter.splitter CaptureStage.wordSplitter
      | .immediate => SignalAdapter.combiner CaptureStage.immediateCombiner
      | .storedNext => SignalAdapter.combinerWithNaming CaptureStage.storedCombiner storedType
      | .stored => Modules.EnabledRegister.Naming.namingWith CaptureStage.storedType storedType
      | .storedOutputs => SignalAdapter.splitterWithNaming CaptureStage.storedSplitter storedType
      | .branch => Modules.EnabledResetRegister.Naming.naming .bit false)

def namedModule : NamedModule where
  ports := CaptureStage.ports
  moduleStructure := CaptureStage.moduleStructure
  naming := naming

end Silean.Examples.PicoRV.Decoder.CaptureStage.Naming
