import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Examples.PicoRV.Alu

namespace Silean.Examples.PicoRV.Datapath

open Silean
open Silean.Authoring

attribute [local simp] SignalMap.set_other

/-! Behavioral contract for the registered datapath in the selected PicoRV32
configuration. It is the value-carrying part of the source's main state
machine: PC flow, operand capture, ALU-result capture, effective addresses,
load results, writeback selection, and the iterative shifter.

`cpu_state` and the `latched_*`/`mem_do_*` inputs are registered values owned by
the control child. Decoder and register-file values arrive directly from their
own children. State assignments that are `x` in the Verilog are represented by
retaining the previous value; those values are irrelevant on every path where
the source leaves them unspecified. -/

abbrev Word := Fin 32 → Bool
abbrev FiveBits := Fin 5 → Bool
abbrev EightBits := Fin 8 → Bool

inductive State
  | reg_pc | reg_next_pc | reg_op1 | reg_op2 | reg_out | reg_sh | alu_out_q
deriving Enumeration

def stateType : State → SignalType
  | .reg_sh => .vector 5 .bit
  | _ => .vector 32 .bit

@[reducible] def stateMap : SignalMap := EnumeratedMap.of State stateType

module_ports ports where
  input resetn : .bit,
  input cpu_state : .vector 8 .bit,
  input latched_store : .bit,
  input latched_stalu : .bit,
  input latched_branch : .bit,
  input latched_is_lu : .bit,
  input latched_is_lh : .bit,
  input latched_is_lb : .bit,
  input mem_do_prefetch : .bit,
  input mem_do_rdata : .bit,
  input mem_do_wdata : .bit,
  input decoder_trigger : .bit,
  input instr_lui : .bit,
  input instr_jal : .bit,
  input instr_sub : .bit,
  input instr_beq : .bit,
  input instr_bne : .bit,
  input instr_bge : .bit,
  input instr_bgeu : .bit,
  input instr_xori : .bit,
  input instr_xor : .bit,
  input instr_ori : .bit,
  input instr_or : .bit,
  input instr_andi : .bit,
  input instr_and : .bit,
  input instr_slli : .bit,
  input instr_srli : .bit,
  input instr_srai : .bit,
  input instr_sll : .bit,
  input instr_srl : .bit,
  input instr_sra : .bit,
  input is_lui_auipc_jal : .bit,
  input is_lb_lh_lw_lbu_lhu : .bit,
  input is_slli_srli_srai : .bit,
  input is_jalr_addi_slti_sltiu_xori_ori_andi : .bit,
  input is_lui_auipc_jal_jalr_addi_add_sub : .bit,
  input is_slti_blt_slt : .bit,
  input is_sltiu_bltu_sltu : .bit,
  input is_compare : .bit,
  input decoded_imm : .vector 32 .bit,
  input decoded_imm_j : .vector 32 .bit,
  input decoded_rs2 : .vector 5 .bit,
  input cpuregs_rs1 : .vector 32 .bit,
  input cpuregs_rs2 : .vector 32 .bit,
  input mem_done : .bit,
  input mem_rdata_word : .vector 32 .bit,
  output reg_pc : .vector 32 .bit,
  output reg_op1 : .vector 32 .bit,
  output reg_op2 : .vector 32 .bit,
  output reg_sh : .vector 5 .bit,
  output next_pc : .vector 32 .bit,
  output alu_out_0 : .bit,
  output cpuregs_wrdata : .vector 32 .bit

structure Inputs where
  resetn : Bool
  cpu_state : EightBits
  latched_store : Bool
  latched_stalu : Bool
  latched_branch : Bool
  latched_is_lu : Bool
  latched_is_lh : Bool
  latched_is_lb : Bool
  mem_do_prefetch : Bool
  mem_do_rdata : Bool
  mem_do_wdata : Bool
  decoder_trigger : Bool
  instr_lui : Bool
  instr_jal : Bool
  instr_sub : Bool
  instr_beq : Bool
  instr_bne : Bool
  instr_bge : Bool
  instr_bgeu : Bool
  instr_xori : Bool
  instr_xor : Bool
  instr_ori : Bool
  instr_or : Bool
  instr_andi : Bool
  instr_and : Bool
  instr_slli : Bool
  instr_srli : Bool
  instr_srai : Bool
  instr_sll : Bool
  instr_srl : Bool
  instr_sra : Bool
  is_lui_auipc_jal : Bool
  is_lb_lh_lw_lbu_lhu : Bool
  is_slli_srli_srai : Bool
  is_jalr_addi_slti_sltiu_xori_ori_andi : Bool
  is_lui_auipc_jal_jalr_addi_add_sub : Bool
  is_slti_blt_slt : Bool
  is_sltiu_bltu_sltu : Bool
  is_compare : Bool
  decoded_imm : Word
  decoded_imm_j : Word
  decoded_rs2 : FiveBits
  cpuregs_rs1 : Word
  cpuregs_rs2 : Word
  mem_done : Bool
  mem_rdata_word : Word

def inputsOfValues (values : inputMap.Values) : Inputs where
  resetn := values .resetn
  cpu_state := values .cpu_state
  latched_store := values .latched_store
  latched_stalu := values .latched_stalu
  latched_branch := values .latched_branch
  latched_is_lu := values .latched_is_lu
  latched_is_lh := values .latched_is_lh
  latched_is_lb := values .latched_is_lb
  mem_do_prefetch := values .mem_do_prefetch
  mem_do_rdata := values .mem_do_rdata
  mem_do_wdata := values .mem_do_wdata
  decoder_trigger := values .decoder_trigger
  instr_lui := values .instr_lui
  instr_jal := values .instr_jal
  instr_sub := values .instr_sub
  instr_beq := values .instr_beq
  instr_bne := values .instr_bne
  instr_bge := values .instr_bge
  instr_bgeu := values .instr_bgeu
  instr_xori := values .instr_xori
  instr_xor := values .instr_xor
  instr_ori := values .instr_ori
  instr_or := values .instr_or
  instr_andi := values .instr_andi
  instr_and := values .instr_and
  instr_slli := values .instr_slli
  instr_srli := values .instr_srli
  instr_srai := values .instr_srai
  instr_sll := values .instr_sll
  instr_srl := values .instr_srl
  instr_sra := values .instr_sra
  is_lui_auipc_jal := values .is_lui_auipc_jal
  is_lb_lh_lw_lbu_lhu := values .is_lb_lh_lw_lbu_lhu
  is_slli_srli_srai := values .is_slli_srli_srai
  is_jalr_addi_slti_sltiu_xori_ori_andi :=
    values .is_jalr_addi_slti_sltiu_xori_ori_andi
  is_lui_auipc_jal_jalr_addi_add_sub :=
    values .is_lui_auipc_jal_jalr_addi_add_sub
  is_slti_blt_slt := values .is_slti_blt_slt
  is_sltiu_bltu_sltu := values .is_sltiu_bltu_sltu
  is_compare := values .is_compare
  decoded_imm := values .decoded_imm
  decoded_imm_j := values .decoded_imm_j
  decoded_rs2 := values .decoded_rs2
  cpuregs_rs1 := values .cpuregs_rs1
  cpuregs_rs2 := values .cpuregs_rs2
  mem_done := values .mem_done
  mem_rdata_word := values .mem_rdata_word

def inputValues (inputs : Inputs) : inputMap.Values
  | .resetn => inputs.resetn
  | .cpu_state => inputs.cpu_state
  | .latched_store => inputs.latched_store
  | .latched_stalu => inputs.latched_stalu
  | .latched_branch => inputs.latched_branch
  | .latched_is_lu => inputs.latched_is_lu
  | .latched_is_lh => inputs.latched_is_lh
  | .latched_is_lb => inputs.latched_is_lb
  | .mem_do_prefetch => inputs.mem_do_prefetch
  | .mem_do_rdata => inputs.mem_do_rdata
  | .mem_do_wdata => inputs.mem_do_wdata
  | .decoder_trigger => inputs.decoder_trigger
  | .instr_lui => inputs.instr_lui
  | .instr_jal => inputs.instr_jal
  | .instr_sub => inputs.instr_sub
  | .instr_beq => inputs.instr_beq
  | .instr_bne => inputs.instr_bne
  | .instr_bge => inputs.instr_bge
  | .instr_bgeu => inputs.instr_bgeu
  | .instr_xori => inputs.instr_xori
  | .instr_xor => inputs.instr_xor
  | .instr_ori => inputs.instr_ori
  | .instr_or => inputs.instr_or
  | .instr_andi => inputs.instr_andi
  | .instr_and => inputs.instr_and
  | .instr_slli => inputs.instr_slli
  | .instr_srli => inputs.instr_srli
  | .instr_srai => inputs.instr_srai
  | .instr_sll => inputs.instr_sll
  | .instr_srl => inputs.instr_srl
  | .instr_sra => inputs.instr_sra
  | .is_lui_auipc_jal => inputs.is_lui_auipc_jal
  | .is_lb_lh_lw_lbu_lhu => inputs.is_lb_lh_lw_lbu_lhu
  | .is_slli_srli_srai => inputs.is_slli_srli_srai
  | .is_jalr_addi_slti_sltiu_xori_ori_andi =>
      inputs.is_jalr_addi_slti_sltiu_xori_ori_andi
  | .is_lui_auipc_jal_jalr_addi_add_sub =>
      inputs.is_lui_auipc_jal_jalr_addi_add_sub
  | .is_slti_blt_slt => inputs.is_slti_blt_slt
  | .is_sltiu_bltu_sltu => inputs.is_sltiu_bltu_sltu
  | .is_compare => inputs.is_compare
  | .decoded_imm => inputs.decoded_imm
  | .decoded_imm_j => inputs.decoded_imm_j
  | .decoded_rs2 => inputs.decoded_rs2
  | .cpuregs_rs1 => inputs.cpuregs_rs1
  | .cpuregs_rs2 => inputs.cpuregs_rs2
  | .mem_done => inputs.mem_done
  | .mem_rdata_word => inputs.mem_rdata_word

@[simp] theorem inputsOfValues_inputValues (inputs : Inputs) :
    inputsOfValues (inputValues inputs) = inputs := by
  cases inputs
  rfl

def wordOfNat (value : Nat) : Word := fun index => value.testBit index.val
def fiveBitsOfNat (value : Nat) : FiveBits := fun index => value.testBit index.val
def stateBits (value : Nat) : EightBits := fun index => value.testBit index.val
def lowFiveBits (value : Word) : FiveBits := fun index => value ⟨index.val, by omega⟩

def stateNumber (inputs : Inputs) : Nat := BitVector.toNat 8 inputs.cpu_state
def shiftAmount (state : stateMap.Values) : Nat := BitVector.toNat 5 (state .reg_sh)

def cpuStateTrap : Nat := 0x80
def cpuStateFetch : Nat := 0x40
def cpuStateLdRs1 : Nat := 0x20
def cpuStateLdRs2 : Nat := 0x10
def cpuStateExec : Nat := 0x08
def cpuStateShift : Nat := 0x04
def cpuStateStmem : Nat := 0x02
def cpuStateLdmem : Nat := 0x01

def addWords (left right : Word) : Word :=
  wordOfNat (BitVector.toNat 32 left + BitVector.toNat 32 right)

def clearLowBit (word : Word) : Word :=
  wordOfNat (BitVector.toNat 32 word / 2 * 2)

def signExtended16 (word : Word) : Word :=
  let value := BitVector.toNat 32 word % 65536
  wordOfNat (if value < 0x8000 then value else value + 0xffff0000)

def signExtended8 (word : Word) : Word :=
  let value := BitVector.toNat 32 word % 256
  wordOfNat (if value < 0x80 then value else value + 0xffffff00)

def shiftLeft (word : Word) (amount : Nat) : Word :=
  wordOfNat (BitVector.toNat 32 word * 2 ^ amount)

def shiftRightLogical (word : Word) (amount : Nat) : Word :=
  wordOfNat (BitVector.toNat 32 word / 2 ^ amount)

def shiftRightArithmetic (word : Word) (amount : Nat) : Word :=
  let shifted := BitVector.toNat 32 word / 2 ^ amount
  if word 31 then wordOfNat (shifted + (2 ^ 32 - 2 ^ (32 - amount)))
  else wordOfNat shifted

def shiftedValue (inputs : Inputs) (word : Word) (amount : Nat) : Word :=
  if inputs.instr_slli || inputs.instr_sll then shiftLeft word amount
  else if inputs.instr_srli || inputs.instr_srl then shiftRightLogical word amount
  else if inputs.instr_srai || inputs.instr_sra then shiftRightArithmetic word amount
  else word

def aluInputs (inputs : Inputs) (state : stateMap.Values) : Alu.Values where
  reg_op1 := state .reg_op1
  reg_op2 := state .reg_op2
  instr_sub := inputs.instr_sub
  instr_beq := inputs.instr_beq
  instr_bne := inputs.instr_bne
  instr_bge := inputs.instr_bge
  instr_bgeu := inputs.instr_bgeu
  is_slti_blt_slt := inputs.is_slti_blt_slt
  is_sltiu_bltu_sltu := inputs.is_sltiu_bltu_sltu
  is_lui_auipc_jal_jalr_addi_add_sub := inputs.is_lui_auipc_jal_jalr_addi_add_sub
  is_compare := inputs.is_compare
  instr_xori := inputs.instr_xori
  instr_xor := inputs.instr_xor
  instr_ori := inputs.instr_ori
  instr_or := inputs.instr_or
  instr_andi := inputs.instr_andi
  instr_and := inputs.instr_and

def aluResult (inputs : Inputs) (state : stateMap.Values) : Word :=
  (Alu.evaluate (aluInputs inputs state)).alu_out

def aluComparison (inputs : Inputs) (state : stateMap.Values) : Bool :=
  (Alu.evaluate (aluInputs inputs state)).alu_out_0

def nextPcFrom (latchedStore latchedBranch : Bool)
    (state : stateMap.Values) : Word :=
  if latchedStore && latchedBranch then clearLowBit (state .reg_out)
  else state .reg_next_pc

def nextPcOutput (inputs : Inputs) (state : stateMap.Values) : Word :=
  nextPcFrom inputs.latched_store inputs.latched_branch state

def writebackFrom (phase : Nat) (latchedStore latchedStalu latchedBranch : Bool)
    (state : stateMap.Values) : Word :=
  if decide (phase = cpuStateFetch) then
    if latchedBranch then addWords (state .reg_pc) (wordOfNat 4)
    else if latchedStore then
      if latchedStalu then state .alu_out_q else state .reg_out
    else wordOfNat 0
  else wordOfNat 0

def writebackData (inputs : Inputs) (state : stateMap.Values) : Word :=
  writebackFrom (stateNumber inputs) inputs.latched_store inputs.latched_stalu
    inputs.latched_branch state

def outputValues (inputs : Inputs) (state : stateMap.Values) : outputMap.Values
  | .reg_pc => state .reg_pc
  | .reg_op1 => state .reg_op1
  | .reg_op2 => state .reg_op2
  | .reg_sh => state .reg_sh
  | .next_pc => nextPcOutput inputs state
  | .alu_out_0 => aluComparison inputs state
  | .cpuregs_wrdata => writebackData inputs state

def fetchNextState (inputs : Inputs) (current updated : stateMap.Values) : stateMap.Values :=
  let currentPc :=
    if inputs.latched_branch && inputs.latched_store then
      clearLowBit (if inputs.latched_stalu then current .alu_out_q else current .reg_out)
    else current .reg_next_pc
  let updated := stateMap.set updated .reg_pc currentPc
  let updated := stateMap.set updated .reg_next_pc currentPc
  if inputs.decoder_trigger then
    stateMap.set updated .reg_next_pc
      (addWords currentPc (if inputs.instr_jal then inputs.decoded_imm_j else wordOfNat 4))
  else updated

def loadRs1NextState (inputs : Inputs) (current updated : stateMap.Values) : stateMap.Values :=
  if inputs.is_lui_auipc_jal then
    let updated := stateMap.set updated .reg_op1
      (if inputs.instr_lui then wordOfNat 0 else current .reg_pc)
    stateMap.set updated .reg_op2 inputs.decoded_imm
  else if inputs.is_lb_lh_lw_lbu_lhu then
    stateMap.set updated .reg_op1 inputs.cpuregs_rs1
  else if inputs.is_slli_srli_srai then
    let updated := stateMap.set updated .reg_op1 inputs.cpuregs_rs1
    stateMap.set updated .reg_sh inputs.decoded_rs2
  else if inputs.is_jalr_addi_slti_sltiu_xori_ori_andi then
    let updated := stateMap.set updated .reg_op1 inputs.cpuregs_rs1
    stateMap.set updated .reg_op2 inputs.decoded_imm
  else
    let updated := stateMap.set updated .reg_op1 inputs.cpuregs_rs1
    let updated := stateMap.set updated .reg_op2 inputs.cpuregs_rs2
    stateMap.set updated .reg_sh (lowFiveBits inputs.cpuregs_rs2)

def shiftNextState (inputs : Inputs) (current updated : stateMap.Values) : stateMap.Values :=
  match shiftAmount current with
  | 0 => stateMap.set updated .reg_out (current .reg_op1)
  | amount =>
      let step := if amount ≥ 4 then 4 else 1
      let updated := stateMap.set updated .reg_op1
        (shiftedValue inputs (current .reg_op1) step)
      stateMap.set updated .reg_sh (fiveBitsOfNat (amount - step))

def loadResult (inputs : Inputs) : Word :=
  if inputs.latched_is_lu then inputs.mem_rdata_word
  else if inputs.latched_is_lh then signExtended16 inputs.mem_rdata_word
  else if inputs.latched_is_lb then signExtended8 inputs.mem_rdata_word
  else wordOfNat 0

def memoryNextState (isLoad : Bool) (inputs : Inputs)
    (current updated : stateMap.Values) : stateMap.Values :=
  if inputs.mem_do_prefetch && !inputs.mem_done then updated else
  let active := if isLoad then inputs.mem_do_rdata else inputs.mem_do_wdata
  let updated := if !active then
      stateMap.set updated .reg_op1 (addWords (current .reg_op1) inputs.decoded_imm)
    else updated
  if isLoad && !inputs.mem_do_prefetch && inputs.mem_done then
    stateMap.set updated .reg_out (loadResult inputs)
  else updated

def normalNextState (inputs : Inputs) (current updated : stateMap.Values) : stateMap.Values :=
  let phase := stateNumber inputs
  if phase = cpuStateFetch then fetchNextState inputs current updated
  else if phase = cpuStateLdRs1 then loadRs1NextState inputs current updated
  else if phase = cpuStateLdRs2 then
    let updated := stateMap.set updated .reg_op2 inputs.cpuregs_rs2
    stateMap.set updated .reg_sh (lowFiveBits inputs.cpuregs_rs2)
  else if phase = cpuStateExec then
    stateMap.set updated .reg_out (addWords (current .reg_pc) inputs.decoded_imm)
  else if phase = cpuStateShift then shiftNextState inputs current updated
  else if phase = cpuStateStmem then memoryNextState false inputs current updated
  else if phase = cpuStateLdmem then memoryNextState true inputs current updated
  else updated

def nextState (inputs : Inputs) (state : stateMap.Values) : stateMap.Values :=
  let updated := stateMap.set state .alu_out_q (aluResult inputs state)
  if !inputs.resetn then
    let updated := stateMap.set updated .reg_pc (wordOfNat 0)
    stateMap.set updated .reg_next_pc (wordOfNat 0)
  else normalNextState inputs state updated

namespace RegisteredRule
inductive Output | reg_pc | reg_op1 | reg_op2 | reg_sh deriving Enumeration
end RegisteredRule

namespace NextPcRule
inductive Input | latched_store | latched_branch deriving Enumeration
inductive Output | next_pc deriving Enumeration
end NextPcRule

namespace ComparisonRule
inductive Input
  | instr_beq | instr_bne | instr_bge | instr_bgeu
  | is_slti_blt_slt | is_sltiu_bltu_sltu
deriving Enumeration
inductive Output | alu_out_0 deriving Enumeration
end ComparisonRule

namespace WritebackRule
inductive Input | cpu_state | latched_store | latched_stalu | latched_branch
deriving Enumeration
inductive Output | cpuregs_wrdata deriving Enumeration
end WritebackRule

@[reducible] private def registeredOutputs : SignalGroup outputMap :=
  SignalGroup.fromLabels outputMap RegisteredRule.Output fun
    | .reg_pc => .reg_pc
    | .reg_op1 => .reg_op1
    | .reg_op2 => .reg_op2
    | .reg_sh => .reg_sh

@[reducible] private def nextPcInputs : SignalGroup inputMap :=
  SignalGroup.fromLabels inputMap NextPcRule.Input fun
    | .latched_store => .latched_store
    | .latched_branch => .latched_branch

@[reducible] private def nextPcOutputs : SignalGroup outputMap :=
  SignalGroup.fromLabels outputMap NextPcRule.Output fun
    | .next_pc => .next_pc

@[reducible] private def comparisonInputs : SignalGroup inputMap :=
  SignalGroup.fromLabels inputMap ComparisonRule.Input fun
    | .instr_beq => .instr_beq
    | .instr_bne => .instr_bne
    | .instr_bge => .instr_bge
    | .instr_bgeu => .instr_bgeu
    | .is_slti_blt_slt => .is_slti_blt_slt
    | .is_sltiu_bltu_sltu => .is_sltiu_bltu_sltu

@[reducible] private def comparisonOutputs : SignalGroup outputMap :=
  SignalGroup.fromLabels outputMap ComparisonRule.Output fun
    | .alu_out_0 => .alu_out_0

@[reducible] private def writebackInputs : SignalGroup inputMap :=
  SignalGroup.fromLabels inputMap WritebackRule.Input fun
    | .cpu_state => .cpu_state
    | .latched_store => .latched_store
    | .latched_stalu => .latched_stalu
    | .latched_branch => .latched_branch

@[reducible] private def writebackOutputs : SignalGroup outputMap :=
  SignalGroup.fromLabels outputMap WritebackRule.Output fun
    | .cpuregs_wrdata => .cpuregs_wrdata

def registeredRule : Contracts.Cycle.CycleOutputRule ports stateMap where
  readsInputs := .empty inputMap
  writesOutputs := registeredOutputs
  target _ state := fun
    | .reg_pc => state .reg_pc
    | .reg_op1 => state .reg_op1
    | .reg_op2 => state .reg_op2
    | .reg_sh => state .reg_sh

def nextPcRule : Contracts.Cycle.CycleOutputRule ports stateMap where
  readsInputs := nextPcInputs
  writesOutputs := nextPcOutputs
  target inputs state := fun
    | .next_pc => nextPcFrom (inputs .latched_store) (inputs .latched_branch) state

def comparisonRule : Contracts.Cycle.CycleOutputRule ports stateMap where
  readsInputs := comparisonInputs
  writesOutputs := comparisonOutputs
  target inputs state := fun
    | .alu_out_0 =>
      let aluInputs : Alu.Values := {
      reg_op1 := state .reg_op1
      reg_op2 := state .reg_op2
      instr_sub := false
      instr_beq := inputs .instr_beq
      instr_bne := inputs .instr_bne
      instr_bge := inputs .instr_bge
      instr_bgeu := inputs .instr_bgeu
      is_slti_blt_slt := inputs .is_slti_blt_slt
      is_sltiu_bltu_sltu := inputs .is_sltiu_bltu_sltu
      is_lui_auipc_jal_jalr_addi_add_sub := false
      is_compare := false
      instr_xori := false
      instr_xor := false
      instr_ori := false
      instr_or := false
      instr_andi := false
      instr_and := false
    }
      Alu.comparisonOutput aluInputs

def writebackRule : Contracts.Cycle.CycleOutputRule ports stateMap where
  readsInputs := writebackInputs
  writesOutputs := writebackOutputs
  target inputs state := fun
    | .cpuregs_wrdata =>
      writebackFrom (BitVector.toNat 8 (inputs .cpu_state))
        (inputs .latched_store) (inputs .latched_stalu)
        (inputs .latched_branch) state

def stateRule : Contracts.Cycle.CycleStateRule ports stateMap where
  readsInputs := .all inputMap
  target := fun inputs state => nextState (inputsOfValues inputs) state

module_cycle_contract cycleContract for ports where
  state := stateMap
  output_rule registered := registeredRule
  output_rule nextPc := nextPcRule
  output_rule comparison := comparisonRule
  output_rule writeback := writebackRule
  state_rule := stateRule

end Silean.Examples.PicoRV.Datapath
