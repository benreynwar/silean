import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Authoring.SignalSchemaDeclaration
import PicoRV.Memory

namespace PicoRV.Control

open Silean
open Silean.Authoring

attribute [local simp] Silean.SignalMap.set_other

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

/-! ## Control-state hardware layout

The cycle contract and the structural implementation share this named tuple.
Its field order follows the source-level control registers and its schema keeps
those names when the aggregate is packed, stored, muxed, or emitted. -/

signal_schema ControlState where
  cpu_state : Silean.Authoring.SignalSchema.vector 8 Silean.Authoring.SignalSchema.bit,
  latched_store : Silean.Authoring.SignalSchema.bit,
  latched_stalu : Silean.Authoring.SignalSchema.bit,
  latched_branch : Silean.Authoring.SignalSchema.bit,
  latched_is_lu : Silean.Authoring.SignalSchema.bit,
  latched_is_lh : Silean.Authoring.SignalSchema.bit,
  latched_is_lb : Silean.Authoring.SignalSchema.bit,
  latched_rd : Silean.Authoring.SignalSchema.vector 5 Silean.Authoring.SignalSchema.bit,
  mem_wordsize : Silean.Authoring.SignalSchema.vector 2 Silean.Authoring.SignalSchema.bit,
  mem_do_prefetch : Silean.Authoring.SignalSchema.bit,
  mem_do_rinst : Silean.Authoring.SignalSchema.bit,
  mem_do_rdata : Silean.Authoring.SignalSchema.bit,
  mem_do_wdata : Silean.Authoring.SignalSchema.bit,
  decoder_trigger : Silean.Authoring.SignalSchema.bit,
  decoder_pseudo_trigger : Silean.Authoring.SignalSchema.bit,
  trap : Silean.Authoring.SignalSchema.bit

abbrev Register := ControlState.Field

@[reducible] def stateMap : SignalMap := ControlState.signalMap

@[reducible] def stateType : SignalType := stateMap.tupleType

module_ports ports where
  input resetn : .bit,
  input instr_jal : .bit,
  input instr_jalr : .bit,
  input instr_lb : .bit,
  input instr_lbu : .bit,
  input instr_lh : .bit,
  input instr_lhu : .bit,
  input instr_lw : .bit,
  input instr_sb : .bit,
  input instr_sh : .bit,
  input instr_sw : .bit,
  input instr_trap : .bit,
  input is_lui_auipc_jal : .bit,
  input is_lb_lh_lw_lbu_lhu : .bit,
  input is_slli_srli_srai : .bit,
  input is_jalr_addi_slti_sltiu_xori_ori_andi : .bit,
  input is_sb_sh_sw : .bit,
  input is_sll_srl_sra : .bit,
  input is_beq_bne_blt_bge_bltu_bgeu : .bit,
  input is_lbu_lhu_lw : .bit,
  input decoded_rd : .vector 5 .bit,
  input reg_pc : .vector 32 .bit,
  input reg_op1 : .vector 32 .bit,
  input reg_sh : .vector 5 .bit,
  input alu_out_0 : .bit,
  input mem_done : .bit,
  output cpuregs_write : .bit,
  output cpu_state : .vector 8 .bit,
  output latched_store : .bit,
  output latched_stalu : .bit,
  output latched_branch : .bit,
  output latched_is_lu : .bit,
  output latched_is_lh : .bit,
  output latched_is_lb : .bit,
  output latched_rd : .vector 5 .bit,
  output mem_wordsize : .vector 2 .bit,
  output mem_do_prefetch : .bit,
  output mem_do_rinst : .bit,
  output mem_do_rdata : .bit,
  output mem_do_wdata : .bit,
  output decoder_trigger : .bit,
  output decoder_pseudo_trigger : .bit,
  output trap : .bit

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

/-! `ControlInputs` is the structural representation shared by the
combinational Control children. A child may inspect only part of this tuple,
but carrying the common named boundary keeps its contract stated directly in
terms of `Inputs` and makes parent composition readable. -/

signal_schema ControlInputs where
  resetn : Silean.Authoring.SignalSchema.bit,
  instr_jal : Silean.Authoring.SignalSchema.bit,
  instr_jalr : Silean.Authoring.SignalSchema.bit,
  instr_lb : Silean.Authoring.SignalSchema.bit,
  instr_lbu : Silean.Authoring.SignalSchema.bit,
  instr_lh : Silean.Authoring.SignalSchema.bit,
  instr_lhu : Silean.Authoring.SignalSchema.bit,
  instr_lw : Silean.Authoring.SignalSchema.bit,
  instr_sb : Silean.Authoring.SignalSchema.bit,
  instr_sh : Silean.Authoring.SignalSchema.bit,
  instr_sw : Silean.Authoring.SignalSchema.bit,
  instr_trap : Silean.Authoring.SignalSchema.bit,
  is_lui_auipc_jal : Silean.Authoring.SignalSchema.bit,
  is_lb_lh_lw_lbu_lhu : Silean.Authoring.SignalSchema.bit,
  is_slli_srli_srai : Silean.Authoring.SignalSchema.bit,
  is_jalr_addi_slti_sltiu_xori_ori_andi : Silean.Authoring.SignalSchema.bit,
  is_sb_sh_sw : Silean.Authoring.SignalSchema.bit,
  is_sll_srl_sra : Silean.Authoring.SignalSchema.bit,
  is_beq_bne_blt_bge_bltu_bgeu : Silean.Authoring.SignalSchema.bit,
  is_lbu_lhu_lw : Silean.Authoring.SignalSchema.bit,
  decoded_rd : Silean.Authoring.SignalSchema.vector 5 Silean.Authoring.SignalSchema.bit,
  reg_pc : Silean.Authoring.SignalSchema.vector 32 Silean.Authoring.SignalSchema.bit,
  reg_op1 : Silean.Authoring.SignalSchema.vector 32 Silean.Authoring.SignalSchema.bit,
  reg_sh : Silean.Authoring.SignalSchema.vector 5 Silean.Authoring.SignalSchema.bit,
  alu_out_0 : Silean.Authoring.SignalSchema.bit,
  mem_done : Silean.Authoring.SignalSchema.bit

@[reducible] def inputsType : SignalType := ControlInputs.signalMap.tupleType

def Inputs.toValues (inputs : Inputs) : ControlInputs.signalMap.Values
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

def Inputs.pack (inputs : Inputs) : inputsType.Denote :=
  ControlInputs.signalMap.pack inputs.toValues

def Inputs.unpack (value : inputsType.Denote) : Inputs :=
  let fields := ControlInputs.signalMap.unpack value
  { resetn := fields .resetn
    instr_jal := fields .instr_jal
    instr_jalr := fields .instr_jalr
    instr_lb := fields .instr_lb
    instr_lbu := fields .instr_lbu
    instr_lh := fields .instr_lh
    instr_lhu := fields .instr_lhu
    instr_lw := fields .instr_lw
    instr_sb := fields .instr_sb
    instr_sh := fields .instr_sh
    instr_sw := fields .instr_sw
    instr_trap := fields .instr_trap
    is_lui_auipc_jal := fields .is_lui_auipc_jal
    is_lb_lh_lw_lbu_lhu := fields .is_lb_lh_lw_lbu_lhu
    is_slli_srli_srai := fields .is_slli_srli_srai
    is_jalr_addi_slti_sltiu_xori_ori_andi :=
      fields .is_jalr_addi_slti_sltiu_xori_ori_andi
    is_sb_sh_sw := fields .is_sb_sh_sw
    is_sll_srl_sra := fields .is_sll_srl_sra
    is_beq_bne_blt_bge_bltu_bgeu := fields .is_beq_bne_blt_bge_bltu_bgeu
    is_lbu_lhu_lw := fields .is_lbu_lhu_lw
    decoded_rd := fields .decoded_rd
    reg_pc := fields .reg_pc
    reg_op1 := fields .reg_op1
    reg_sh := fields .reg_sh
    alu_out_0 := fields .alu_out_0
    mem_done := fields .mem_done }

@[simp] theorem Inputs.unpack_pack (inputs : Inputs) :
    Inputs.unpack inputs.pack = inputs := by
  cases inputs
  simp [Inputs.unpack, Inputs.pack, Inputs.toValues]

@[simp] theorem Inputs.pack_unpack (value : inputsType.Denote) :
    (Inputs.unpack value).pack = value := by
  change (Inputs.unpack value).pack = value
  calc
    (Inputs.unpack value).pack =
        ControlInputs.signalMap.pack (ControlInputs.signalMap.unpack value) := by
      apply congrArg (ControlInputs.signalMap.pack)
      funext field
      cases field <;> simp [Inputs.unpack, Inputs.toValues]
    _ = value := ControlInputs.signalMap.pack_unpack value

/-- Unpacking a packed input tuple and projecting its fields recovers the
underlying signal-map values. -/
theorem Inputs.toValues_unpack (value : inputsType.Denote) :
    (Inputs.unpack value).toValues = ControlInputs.signalMap.unpack value := by
  have packed := congrArg ControlInputs.signalMap.unpack (Inputs.pack_unpack value)
  simpa only [Inputs.pack, ControlInputs.signalMap.unpack_pack] using packed

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

@[simp] theorem inputValues_inputsOfValues (values : inputMap.Values) :
    inputValues (inputsOfValues values) = values := by
  funext input
  cases input <;> rfl

def wordOfNat (value : Nat) : Word := fun index => value.testBit index.val
def twoBitsOfNat (value : Nat) : TwoBits := fun index => value.testBit index.val
def fiveBitsOfNat (value : Nat) : FiveBits := fun index => value.testBit index.val
def stateBits (value : Nat) : EightBits := fun index => value.testBit index.val

def phase (state : stateMap.Values) : Nat := Silean.BitVector.toNat 8 (state .cpu_state)
def wordSize (state : stateMap.Values) : Nat := Silean.BitVector.toNat 2 (state .mem_wordsize)
def shiftAmount (inputs : Inputs) : Nat := Silean.BitVector.toNat 5 inputs.reg_sh

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
  | .cpuregs_write => cpuregsWrite state
  | .cpu_state => state .cpu_state
  | .latched_store => state .latched_store
  | .latched_stalu => state .latched_stalu
  | .latched_branch => state .latched_branch
  | .latched_is_lu => state .latched_is_lu
  | .latched_is_lh => state .latched_is_lh
  | .latched_is_lb => state .latched_is_lb
  | .latched_rd => state .latched_rd
  | .mem_wordsize => state .mem_wordsize
  | .mem_do_prefetch => state .mem_do_prefetch
  | .mem_do_rinst => state .mem_do_rinst
  | .mem_do_rdata => state .mem_do_rdata
  | .mem_do_wdata => state .mem_do_wdata
  | .decoder_trigger => state .decoder_trigger
  | .decoder_pseudo_trigger => state .decoder_pseudo_trigger
  | .trap => state .trap

structure Transition where
  state : stateMap.Values
  setRinst : Bool := false
  setRdata : Bool := false
  setWdata : Bool := false

/-! `TransitionValue` is the structural representation of `Transition`. The
nested state schema preserves all source register names while the three intent
bits remain visibly separate from the proposed state. -/

signal_schema TransitionValue where
  state : ControlState.schema,
  setRinst : Silean.Authoring.SignalSchema.bit,
  setRdata : Silean.Authoring.SignalSchema.bit,
  setWdata : Silean.Authoring.SignalSchema.bit

@[reducible] def transitionType : SignalType := TransitionValue.signalMap.tupleType

def Transition.toValues (transition : Transition) : TransitionValue.signalMap.Values
  | .state => stateMap.pack transition.state
  | .setRinst => transition.setRinst
  | .setRdata => transition.setRdata
  | .setWdata => transition.setWdata

def Transition.pack (transition : Transition) : transitionType.Denote :=
  TransitionValue.signalMap.pack transition.toValues

def Transition.unpack (value : transitionType.Denote) : Transition :=
  let fields := TransitionValue.signalMap.unpack value
  { state := stateMap.unpack (fields .state)
    setRinst := fields .setRinst
    setRdata := fields .setRdata
    setWdata := fields .setWdata }

@[simp] theorem Transition.unpack_pack (transition : Transition) :
    Transition.unpack transition.pack = transition := by
  cases transition
  simp [Transition.unpack, Transition.pack, Transition.toValues]

@[simp] theorem Transition.pack_unpack (value : transitionType.Denote) :
    (Transition.unpack value).pack = value := by
  change (Transition.unpack value).pack = value
  calc
    (Transition.unpack value).pack =
        TransitionValue.signalMap.pack (TransitionValue.signalMap.unpack value) := by
      apply congrArg (TransitionValue.signalMap.pack)
      funext field
      cases field <;> simp [Transition.unpack, Transition.toValues]
    _ = value := TransitionValue.signalMap.pack_unpack value

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
  if inputs.is_sb_sh_sw then
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
        decide (Silean.BitVector.toNat 32 inputs.reg_op1 % 4 ≠ 0)) ||
      (decide (wordSize state = 1) && inputs.reg_op1 0))

def instructionMisaligned (inputs : Inputs) (state : stateMap.Values) : Bool :=
  (state .mem_do_rinst : Bool) && decide (Silean.BitVector.toNat 32 inputs.reg_pc % 4 ≠ 0)

/-! The next-state calculation is named by source-level priority layer so the
structural children can state natural contracts without restating fragments of
`nextState`. These helpers do not introduce new behavior: their order is the
order of the corresponding assignments in the configured Verilog block. -/

def baselineState (inputs : Inputs) (state : stateMap.Values) : stateMap.Values :=
  let baseline := stateMap.set state .trap false
  let baseline := stateMap.set baseline .decoder_trigger
    ((state .mem_do_rinst : Bool) && inputs.mem_done)
  stateMap.set baseline .decoder_pseudo_trigger false

def resetAndAlignmentTransition (inputs : Inputs) (state baseline : stateMap.Values)
    (selected : Transition) : Transition :=
  let transition := if !inputs.resetn then resetTransition baseline
    else selected
  if inputs.resetn &&
      (dataMisaligned inputs state || instructionMisaligned inputs state) then
      { transition with state :=
          (stateMap.set transition.state .cpu_state (stateBits cpuStateTrap)) }
    else transition

def transitionBeforeCommandFinish (inputs : Inputs)
    (state : stateMap.Values) : Transition :=
  let baseline := baselineState inputs state
  let selected := phaseTransition inputs state baseline
  resetAndAlignmentTransition inputs state baseline selected

def nextState (inputs : Inputs) (state : stateMap.Values) : stateMap.Values :=
  let baseline := baselineState inputs state
  let selected := phaseTransition inputs state baseline
  let transition := resetAndAlignmentTransition inputs state baseline selected
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

def outputRule : Silean.Contracts.Cycle.CycleOutputRule ports stateMap where
  readsInputs := .empty inputMap
  writesOutputs := .all outputMap
  target _ state := outputValues state

@[simp] theorem outputRule_holds_iff (inputs : inputMap.Values)
    (state : stateMap.Values) (outputs : outputMap.Values) :
    outputRule.Holds inputs state outputs ↔ outputs = outputValues state := by
  simp [Silean.Contracts.Cycle.CycleOutputRule.Holds, outputRule,
    Silean.SignalGroup.all_matches]

def stateRule : Silean.Contracts.Cycle.CycleStateRule ports stateMap where
  readsInputs := .all inputMap
  target inputs state := nextState (inputsOfValues inputs) state

module_cycle_contract cycleContract for ports where
  state := stateMap
  output_rule outputs := outputRule
  state_rule := stateRule

end PicoRV.Control
