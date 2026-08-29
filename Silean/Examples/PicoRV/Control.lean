import Silean.Examples.PicoRV.Memory

namespace Silean.Examples.PicoRV.Control

open Silean

attribute [local simp] SignalMap.set_other

/-! Exact cycle contract for the sequencing half of PicoRV32's main state
machine in the selected configuration. Value-carrying registers belong to
`PicoRV32Datapath`; this contract owns processor phase, writeback metadata,
memory commands, decoder triggers, and trap state.

The transition preserves Verilog nonblocking timing. Decisions read the
pre-edge control state, while the three source `set_mem_do_*` blocking
temporaries are represented explicitly and applied after the source's common
command-clear block. -/

abbrev Word := Fin 32 → Bool
abbrev TwoBits := Fin 2 → Bool
abbrev FiveBits := Fin 5 → Bool
abbrev EightBits := Fin 8 → Bool

inductive Input
  | resetn
  | instr_jal | instr_jalr
  | instr_lb | instr_lbu | instr_lh | instr_lhu | instr_lw
  | instr_sb | instr_sh | instr_sw | instr_trap
  | is_lui_auipc_jal | is_lb_lh_lw_lbu_lhu | is_slli_srli_srai
  | is_jalr_addi_slti_sltiu_xori_ori_andi | is_sb_sh_sw | is_sll_srl_sra
  | is_beq_bne_blt_bge_bltu_bgeu | is_lbu_lhu_lw
  | decoded_rd
  | reg_pc | reg_op1 | reg_sh | alu_out_0
  | mem_done
deriving Enumeration

inductive Register
  | cpu_state
  | latched_store | latched_stalu | latched_branch
  | latched_is_lu | latched_is_lh | latched_is_lb | latched_rd
  | mem_wordsize
  | mem_do_prefetch | mem_do_rinst | mem_do_rdata | mem_do_wdata
  | decoder_trigger | decoder_pseudo_trigger | trap
deriving Enumeration

abbrev Output := Sum PUnit Register

instance : Enumeration Output := Enumeration.sum Enumeration.punit inferInstance

namespace Output

def cpuregs_write : Output := .inl .unit
def cpu_state : Output := .inr .cpu_state
def latched_store : Output := .inr .latched_store
def latched_stalu : Output := .inr .latched_stalu
def latched_branch : Output := .inr .latched_branch
def latched_is_lu : Output := .inr .latched_is_lu
def latched_is_lh : Output := .inr .latched_is_lh
def latched_is_lb : Output := .inr .latched_is_lb
def latched_rd : Output := .inr .latched_rd
def mem_wordsize : Output := .inr .mem_wordsize
def mem_do_prefetch : Output := .inr .mem_do_prefetch
def mem_do_rinst : Output := .inr .mem_do_rinst
def mem_do_rdata : Output := .inr .mem_do_rdata
def mem_do_wdata : Output := .inr .mem_do_wdata
def decoder_trigger : Output := .inr .decoder_trigger
def decoder_pseudo_trigger : Output := .inr .decoder_pseudo_trigger
def trap : Output := .inr .trap

end Output

def inputType : Input → SignalType
  | .decoded_rd | .reg_sh => .vector 5 .bit
  | .reg_pc | .reg_op1 => .vector 32 .bit
  | _ => .bit

@[reducible] def inputMap : SignalMap := EnumeratedMap.of Input inputType

def registerType : Register → SignalType
  | .cpu_state => .vector 8 .bit
  | .latched_rd => .vector 5 .bit
  | .mem_wordsize => .vector 2 .bit
  | _ => .bit

@[reducible] def stateMap : SignalMap := EnumeratedMap.of Register registerType

@[reducible] def outputMap : SignalMap :=
  EnumeratedMap.of Output fun
    | .inl .unit => .bit
    | .inr name => registerType name

@[reducible] def ports : ModulePorts := ⟨inputMap, outputMap⟩

structure Inputs where
  resetn : Bool
  instr_jal : Bool
  instr_jalr : Bool
  instr_lb : Bool
  instr_lbu : Bool
  instr_lh : Bool
  instr_lhu : Bool
  instr_lw : Bool
  instr_sb : Bool
  instr_sh : Bool
  instr_sw : Bool
  instr_trap : Bool
  is_lui_auipc_jal : Bool
  is_lb_lh_lw_lbu_lhu : Bool
  is_slli_srli_srai : Bool
  is_jalr_addi_slti_sltiu_xori_ori_andi : Bool
  is_sb_sh_sw : Bool
  is_sll_srl_sra : Bool
  is_beq_bne_blt_bge_bltu_bgeu : Bool
  is_lbu_lhu_lw : Bool
  decoded_rd : FiveBits
  reg_pc : Word
  reg_op1 : Word
  reg_sh : FiveBits
  alu_out_0 : Bool
  mem_done : Bool

def inputsOfValues (values : inputMap.Values) : Inputs where
  resetn := values .resetn
  instr_jal := values .instr_jal
  instr_jalr := values .instr_jalr
  instr_lb := values .instr_lb
  instr_lbu := values .instr_lbu
  instr_lh := values .instr_lh
  instr_lhu := values .instr_lhu
  instr_lw := values .instr_lw
  instr_sb := values .instr_sb
  instr_sh := values .instr_sh
  instr_sw := values .instr_sw
  instr_trap := values .instr_trap
  is_lui_auipc_jal := values .is_lui_auipc_jal
  is_lb_lh_lw_lbu_lhu := values .is_lb_lh_lw_lbu_lhu
  is_slli_srli_srai := values .is_slli_srli_srai
  is_jalr_addi_slti_sltiu_xori_ori_andi :=
    values .is_jalr_addi_slti_sltiu_xori_ori_andi
  is_sb_sh_sw := values .is_sb_sh_sw
  is_sll_srl_sra := values .is_sll_srl_sra
  is_beq_bne_blt_bge_bltu_bgeu := values .is_beq_bne_blt_bge_bltu_bgeu
  is_lbu_lhu_lw := values .is_lbu_lhu_lw
  decoded_rd := values .decoded_rd
  reg_pc := values .reg_pc
  reg_op1 := values .reg_op1
  reg_sh := values .reg_sh
  alu_out_0 := values .alu_out_0
  mem_done := values .mem_done

def inputValues (inputs : Inputs) : inputMap.Values
  | .resetn => inputs.resetn
  | .instr_jal => inputs.instr_jal
  | .instr_jalr => inputs.instr_jalr
  | .instr_lb => inputs.instr_lb
  | .instr_lbu => inputs.instr_lbu
  | .instr_lh => inputs.instr_lh
  | .instr_lhu => inputs.instr_lhu
  | .instr_lw => inputs.instr_lw
  | .instr_sb => inputs.instr_sb
  | .instr_sh => inputs.instr_sh
  | .instr_sw => inputs.instr_sw
  | .instr_trap => inputs.instr_trap
  | .is_lui_auipc_jal => inputs.is_lui_auipc_jal
  | .is_lb_lh_lw_lbu_lhu => inputs.is_lb_lh_lw_lbu_lhu
  | .is_slli_srli_srai => inputs.is_slli_srli_srai
  | .is_jalr_addi_slti_sltiu_xori_ori_andi =>
      inputs.is_jalr_addi_slti_sltiu_xori_ori_andi
  | .is_sb_sh_sw => inputs.is_sb_sh_sw
  | .is_sll_srl_sra => inputs.is_sll_srl_sra
  | .is_beq_bne_blt_bge_bltu_bgeu => inputs.is_beq_bne_blt_bge_bltu_bgeu
  | .is_lbu_lhu_lw => inputs.is_lbu_lhu_lw
  | .decoded_rd => inputs.decoded_rd
  | .reg_pc => inputs.reg_pc
  | .reg_op1 => inputs.reg_op1
  | .reg_sh => inputs.reg_sh
  | .alu_out_0 => inputs.alu_out_0
  | .mem_done => inputs.mem_done

@[simp] theorem inputsOfValues_inputValues (inputs : Inputs) :
    inputsOfValues (inputValues inputs) = inputs := by
  cases inputs
  rfl

def wordOfNat (value : Nat) : Word := fun index => value.testBit index.val
def twoBitsOfNat (value : Nat) : TwoBits := fun index => value.testBit index.val
def fiveBitsOfNat (value : Nat) : FiveBits := fun index => value.testBit index.val
def stateBits (value : Nat) : EightBits := fun index => value.testBit index.val

def phase (state : stateMap.Values) : Nat := BitVector.toNat 8 (state .cpu_state)
def wordSize (state : stateMap.Values) : Nat := BitVector.toNat 2 (state .mem_wordsize)
def shiftAmount (inputs : Inputs) : Nat := BitVector.toNat 5 inputs.reg_sh

def cpuStateTrap : Nat := 0x80
def cpuStateFetch : Nat := 0x40
def cpuStateLdRs1 : Nat := 0x20
def cpuStateLdRs2 : Nat := 0x10
def cpuStateExec : Nat := 0x08
def cpuStateShift : Nat := 0x04
def cpuStateStmem : Nat := 0x02
def cpuStateLdmem : Nat := 0x01

def cpuregsWrite (state : stateMap.Values) : Bool :=
  decide (phase state = cpuStateFetch) &&
    ((state .latched_branch : Bool) || state .latched_store)

def outputValues (state : stateMap.Values) : outputMap.Values
  | .inl .unit => cpuregsWrite state
  | .inr name => state name

structure Transition where
  state : stateMap.Values
  setRinst : Bool := false
  setRdata : Bool := false
  setWdata : Bool := false

def simpleTransition (state : stateMap.Values) : Transition :=
  { state := state }

def fetchTransition (inputs : Inputs) (current updated : stateMap.Values) : Transition :=
  let updated := stateMap.set updated .mem_do_rinst (!(current .decoder_trigger : Bool))
  let updated := stateMap.set updated .mem_wordsize (twoBitsOfNat 0)
  let updated := stateMap.set updated .latched_store false
  let updated := stateMap.set updated .latched_stalu false
  let updated := stateMap.set updated .latched_branch false
  let updated := stateMap.set updated .latched_is_lu false
  let updated := stateMap.set updated .latched_is_lh false
  let updated := stateMap.set updated .latched_is_lb false
  let updated := stateMap.set updated .latched_rd inputs.decoded_rd
  if !(current .decoder_trigger : Bool) then simpleTransition updated else
  let updated := stateMap.set updated .mem_do_rinst false
  if inputs.instr_jal then
    let updated := stateMap.set updated .mem_do_rinst true
    let updated := stateMap.set updated .latched_branch true
    simpleTransition updated
  else
    let updated := stateMap.set updated .mem_do_prefetch (!inputs.instr_jalr)
    simpleTransition (stateMap.set updated .cpu_state (stateBits cpuStateLdRs1))

def loadRs1Transition (inputs : Inputs) (updated : stateMap.Values) : Transition :=
  if inputs.instr_trap then
    simpleTransition (stateMap.set updated .cpu_state (stateBits cpuStateTrap))
  else if inputs.is_lui_auipc_jal then
    let updated := stateMap.set updated .mem_do_rinst (updated .mem_do_prefetch)
    simpleTransition (stateMap.set updated .cpu_state (stateBits cpuStateExec))
  else if inputs.is_lb_lh_lw_lbu_lhu then
    let updated := stateMap.set updated .mem_do_rinst true
    simpleTransition (stateMap.set updated .cpu_state (stateBits cpuStateLdmem))
  else if inputs.is_slli_srli_srai then
    simpleTransition (stateMap.set updated .cpu_state (stateBits cpuStateShift))
  else if inputs.is_jalr_addi_slti_sltiu_xori_ori_andi then
    let updated := stateMap.set updated .mem_do_rinst (updated .mem_do_prefetch)
    simpleTransition (stateMap.set updated .cpu_state (stateBits cpuStateExec))
  else if inputs.is_sb_sh_sw then
    let updated := stateMap.set updated .mem_do_rinst true
    simpleTransition (stateMap.set updated .cpu_state (stateBits cpuStateStmem))
  else if inputs.is_sll_srl_sra then
    simpleTransition (stateMap.set updated .cpu_state (stateBits cpuStateShift))
  else
    let updated := stateMap.set updated .mem_do_rinst (updated .mem_do_prefetch)
    simpleTransition (stateMap.set updated .cpu_state (stateBits cpuStateExec))

def loadRs2Transition (inputs : Inputs) (updated : stateMap.Values) : Transition :=
  if inputs.instr_trap then
    simpleTransition (stateMap.set updated .cpu_state (stateBits cpuStateTrap))
  else if inputs.is_sb_sh_sw then
    let updated := stateMap.set updated .mem_do_rinst true
    simpleTransition (stateMap.set updated .cpu_state (stateBits cpuStateStmem))
  else if inputs.is_sll_srl_sra then
    simpleTransition (stateMap.set updated .cpu_state (stateBits cpuStateShift))
  else
    let updated := stateMap.set updated .mem_do_rinst (updated .mem_do_prefetch)
    simpleTransition (stateMap.set updated .cpu_state (stateBits cpuStateExec))

def executeTransition (inputs : Inputs) (updated : stateMap.Values) : Transition :=
  if inputs.is_beq_bne_blt_bge_bltu_bgeu then
    let updated := stateMap.set updated .latched_rd (fiveBitsOfNat 0)
    let updated := stateMap.set updated .latched_store inputs.alu_out_0
    let updated := stateMap.set updated .latched_branch inputs.alu_out_0
    let updated := if inputs.mem_done then
        stateMap.set updated .cpu_state (stateBits cpuStateFetch)
      else updated
    let updated := if inputs.alu_out_0 then
        stateMap.set updated .decoder_trigger false
      else updated
    { state := updated, setRinst := inputs.alu_out_0 }
  else
    let updated := stateMap.set updated .latched_branch inputs.instr_jalr
    let updated := stateMap.set updated .latched_store true
    let updated := stateMap.set updated .latched_stalu true
    simpleTransition (stateMap.set updated .cpu_state (stateBits cpuStateFetch))

def shiftTransition (inputs : Inputs) (updated : stateMap.Values) : Transition :=
  let updated := stateMap.set updated .latched_store true
  if shiftAmount inputs = 0 then
    let updated := stateMap.set updated .mem_do_rinst (updated .mem_do_prefetch)
    simpleTransition (stateMap.set updated .cpu_state (stateBits cpuStateFetch))
  else simpleTransition updated

def storeTransition (inputs : Inputs) (current updated : stateMap.Values) : Transition :=
  if (current .mem_do_prefetch : Bool) && !inputs.mem_done then
    simpleTransition updated else
  let updated := if !(current .mem_do_wdata : Bool) then
      let size := if inputs.instr_sb then 2 else if inputs.instr_sh then 1 else 0
      stateMap.set updated .mem_wordsize (twoBitsOfNat size)
    else updated
  let finish := !(current .mem_do_prefetch : Bool) && inputs.mem_done
  let updated := if finish then
      let updated := stateMap.set updated .cpu_state (stateBits cpuStateFetch)
      let updated := stateMap.set updated .decoder_trigger true
      stateMap.set updated .decoder_pseudo_trigger true
    else updated
  { state := updated, setWdata := !(current .mem_do_wdata : Bool) }

def loadTransition (inputs : Inputs) (current updated : stateMap.Values) : Transition :=
  let updated := stateMap.set updated .latched_store true
  if (current .mem_do_prefetch : Bool) && !inputs.mem_done then
    simpleTransition updated else
  let starting := !(current .mem_do_rdata : Bool)
  let updated := if starting then
      let size := if inputs.instr_lb || inputs.instr_lbu then 2
        else if inputs.instr_lh || inputs.instr_lhu then 1 else 0
      let updated := stateMap.set updated .mem_wordsize (twoBitsOfNat size)
      let updated := stateMap.set updated .latched_is_lu inputs.is_lbu_lhu_lw
      let updated := stateMap.set updated .latched_is_lh inputs.instr_lh
      stateMap.set updated .latched_is_lb inputs.instr_lb
    else updated
  let finish := !(current .mem_do_prefetch : Bool) && inputs.mem_done
  let updated := if finish then
      let updated := stateMap.set updated .cpu_state (stateBits cpuStateFetch)
      let updated := stateMap.set updated .decoder_trigger true
      stateMap.set updated .decoder_pseudo_trigger true
    else updated
  { state := updated, setRdata := starting }

def phaseTransition (inputs : Inputs) (current updated : stateMap.Values) : Transition :=
  let currentPhase := phase current
  if currentPhase = cpuStateTrap then
    simpleTransition (stateMap.set updated .trap true)
  else if currentPhase = cpuStateFetch then fetchTransition inputs current updated
  else if currentPhase = cpuStateLdRs1 then loadRs1Transition inputs updated
  else if currentPhase = cpuStateLdRs2 then loadRs2Transition inputs updated
  else if currentPhase = cpuStateExec then executeTransition inputs updated
  else if currentPhase = cpuStateShift then shiftTransition inputs updated
  else if currentPhase = cpuStateStmem then storeTransition inputs current updated
  else if currentPhase = cpuStateLdmem then loadTransition inputs current updated
  else simpleTransition updated

def resetTransition (updated : stateMap.Values) : Transition :=
  let updated := stateMap.set updated .latched_store false
  let updated := stateMap.set updated .latched_stalu false
  let updated := stateMap.set updated .latched_branch false
  let updated := stateMap.set updated .latched_is_lu false
  let updated := stateMap.set updated .latched_is_lh false
  let updated := stateMap.set updated .latched_is_lb false
  simpleTransition (stateMap.set updated .cpu_state (stateBits cpuStateFetch))

def commandsCleared (state : stateMap.Values) : stateMap.Values :=
  let state := stateMap.set state .mem_do_prefetch false
  let state := stateMap.set state .mem_do_rinst false
  let state := stateMap.set state .mem_do_rdata false
  stateMap.set state .mem_do_wdata false

def finishCommands (clear : Bool) (transition : Transition) : stateMap.Values :=
  let state := if clear then commandsCleared transition.state else transition.state
  let state := if transition.setRinst then stateMap.set state .mem_do_rinst true else state
  let state := if transition.setRdata then stateMap.set state .mem_do_rdata true else state
  if transition.setWdata then stateMap.set state .mem_do_wdata true else state

def dataMisaligned (inputs : Inputs) (state : stateMap.Values) : Bool :=
  ((state .mem_do_rdata : Bool) || state .mem_do_wdata) &&
    ((decide (wordSize state = 0) &&
        decide (BitVector.toNat 32 inputs.reg_op1 % 4 ≠ 0)) ||
      (decide (wordSize state = 1) && inputs.reg_op1 0))

def instructionMisaligned (inputs : Inputs) (state : stateMap.Values) : Bool :=
  (state .mem_do_rinst : Bool) && decide (BitVector.toNat 32 inputs.reg_pc % 4 ≠ 0)

def nextState (inputs : Inputs) (state : stateMap.Values) : stateMap.Values :=
  let baseline := stateMap.set state .trap false
  let baseline := stateMap.set baseline .decoder_trigger
    ((state .mem_do_rinst : Bool) && inputs.mem_done)
  let baseline := stateMap.set baseline .decoder_pseudo_trigger false
  let transition := if !inputs.resetn then resetTransition baseline
    else phaseTransition inputs state baseline
  let transition := if inputs.resetn &&
      (dataMisaligned inputs state || instructionMisaligned inputs state) then
      { transition with state :=
          (stateMap.set transition.state .cpu_state (stateBits cpuStateTrap)) }
    else transition
  finishCommands (!inputs.resetn || inputs.mem_done) transition

structure Commands where
  mem_do_prefetch : Bool
  mem_do_rinst : Bool
  mem_do_rdata : Bool
  mem_do_wdata : Bool

def commands (state : stateMap.Values) : Commands where
  mem_do_prefetch := state .mem_do_prefetch
  mem_do_rinst := state .mem_do_rinst
  mem_do_rdata := state .mem_do_rdata
  mem_do_wdata := state .mem_do_wdata

def Commands.wellFormed (command : Commands) : Bool :=
  (!command.mem_do_rdata ||
      (!command.mem_do_prefetch && !command.mem_do_rinst && !command.mem_do_wdata)) &&
    (!command.mem_do_wdata ||
      (!command.mem_do_prefetch && !command.mem_do_rinst && !command.mem_do_rdata))

def memoryInputs (inputs : Inputs) (state : stateMap.Values) : Memory.Inputs where
  resetn := inputs.resetn
  trap := state .trap
  mem_do_prefetch := state .mem_do_prefetch
  mem_do_rinst := state .mem_do_rinst
  mem_do_rdata := state .mem_do_rdata
  mem_do_wdata := state .mem_do_wdata
  next_pc := wordOfNat 0
  reg_op1 := inputs.reg_op1
  reg_op2 := wordOfNat 0
  mem_wordsize := state .mem_wordsize
  mem_ready := false
  mem_rdata := wordOfNat 0

theorem commands_wellFormed_iff_memory (inputs : Inputs) (state : stateMap.Values) :
    (commands state).wellFormed = true ↔
      Memory.CommandsWellFormed (memoryInputs inputs state) := by
  simp [Commands.wellFormed, commands, Memory.CommandsWellFormed, memoryInputs]
  constructor
  · intro wellFormed
    constructor <;> intro active
    · simp_all
    · simp_all
  · rintro ⟨read, write⟩
    by_cases rdata : (state .mem_do_rdata : Bool) = true
    · simp_all
    · by_cases wdata : (state .mem_do_wdata : Bool) = true <;> simp_all

inductive Rule | outputs
deriving Enumeration

def outputRule : Contracts.Cycle.CycleOutputRule ports stateMap
    { inputTypes := .nil, outputTypes := .ofList outputMap.types } where
  readsInputs := .nil
  writesOutputs := outputMap.allSelection
  target := fun _ state => outputMap.allSelection.project (outputValues state)

def stateRule : Contracts.Cycle.CycleStateRule ports stateMap where
  inputTypes := .ofList inputMap.types
  readsInputs := inputMap.allSelection
  target := fun selected state => nextState (inputsOfValues (inputMap.unpack selected)) state

@[reducible] def cycleContract : Contracts.Cycle.ModuleCycleContract ports where
  state := stateMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .outputs => ⟨_, outputRule⟩
  stateRule := stateRule
  outputCoverage := by
    change outputMap.allSelection.labels.Perm outputMap.labels.values
    rw [SignalMap.allSelection_labels]

end Silean.Examples.PicoRV.Control
