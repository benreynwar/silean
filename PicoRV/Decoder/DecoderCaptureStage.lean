import PicoRV.Decoder.DecoderTypes
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.CircuitDescription
import PicoRV.Authoring.CircuitLogic
import PicoRV.Decoder.Internal.DecoderCaptureStageStructure

namespace PicoRV.Decoder.CaptureStage

open Silean
open Silean.Authoring
open PicoRV.Decoder

/-! The first registered decoder stage. It captures broad opcode classes,
register addresses, and the J immediate when an instruction read completes.
Only the branch-class register is reset in the selected PicoRV32 source. -/

/-! ## Authored hardware

The thirteen non-reset fields share one aggregate enabled register. The
branch-class flag uses a separate enabled/reset register because the source's
final reset block overrides only that assignment. -/

namespace Description

open Silean.Authoring.CircuitDescription
open PicoRV.Authoring.CircuitLogic
open scoped Silean.Authoring.CircuitLogic

noncomputable def construction : Builder Unit := do
  let resetn ← input "resetn" .bit
  let memDoRinst ← input "mem_do_rinst" .bit
  let memDone ← input "mem_done" .bit
  let word ← input "mem_rdata_latched" (.vector 32 .bit)
  let captureEnable ← memDoRinst &&& memDone
  let reset ← !! resetn
  let opcode ← Silean.Modules.VectorSlice.place
    (element := .bit) (prefixWidth := 0) (width := 7) (suffixWidth := 25) word
  let funct3 ← Silean.Modules.VectorSlice.place
    (element := .bit) (prefixWidth := 12) (width := 3) (suffixWidth := 17) word
  let decodedRd ← Silean.Modules.VectorSlice.place
    (element := .bit) (prefixWidth := 7) (width := 5) (suffixWidth := 20) word
  let decodedRs1 ← Silean.Modules.VectorSlice.place
    (element := .bit) (prefixWidth := 15) (width := 5) (suffixWidth := 12) word
  let decodedRs2 ← Silean.Modules.VectorSlice.place
    (element := .bit) (prefixWidth := 20) (width := 5) (suffixWidth := 7) word
  let opcodeLui ← Silean.Modules.EqualsConstant.place opcode (bits 7 0x37)
  let opcodeAuipc ← Silean.Modules.EqualsConstant.place opcode (bits 7 0x17)
  let opcodeJal ← Silean.Modules.EqualsConstant.place opcode (bits 7 0x6f)
  let opcodeJalr ← Silean.Modules.EqualsConstant.place opcode (bits 7 0x67)
  let opcodeBranch ← Silean.Modules.EqualsConstant.place opcode (bits 7 0x63)
  let opcodeLoad ← Silean.Modules.EqualsConstant.place opcode (bits 7 0x03)
  let opcodeStore ← Silean.Modules.EqualsConstant.place opcode (bits 7 0x23)
  let opcodeAluImm ← Silean.Modules.EqualsConstant.place opcode (bits 7 0x13)
  let opcodeAluReg ← Silean.Modules.EqualsConstant.place opcode (bits 7 0x33)
  let funct3Zero ← Silean.Modules.EqualsConstant.place funct3 (bits 3 0)
  let jalr ← opcodeJalr &&& funct3Zero
  let zero ← constant .bit false
  let immediate ← Silean.Modules.VectorLayout.place immediateJLayout word
  let storedNext ← combine storedMap Stored.schema fun
    | .instr_lui => opcodeLui
    | .instr_auipc => opcodeAuipc
    | .instr_jal => opcodeJal
    | .instr_jalr => jalr
    | .decoded_rd => decodedRd
    | .decoded_rs1 => decodedRs1
    | .decoded_rs2 => decodedRs2
    | .decoded_imm_j => immediate
    | .compressed_instr => zero
    | .is_lb_lh_lw_lbu_lhu => opcodeLoad
    | .is_sb_sh_sw => opcodeStore
    | .is_alu_reg_imm => opcodeAluImm
    | .is_alu_reg_reg => opcodeAluReg
  let stored ← Silean.Modules.EnabledRegister.placeWith Stored.schema
    storedNext captureEnable
  let storedOutputs ← split Stored.layout stored
  let branch ← Silean.Modules.EnabledResetRegister.place (signalType := .bit)
    false opcodeBranch captureEnable reset

  output "instr_lui" (storedOutputs .instr_lui)
  output "instr_auipc" (storedOutputs .instr_auipc)
  output "instr_jal" (storedOutputs .instr_jal)
  output "instr_jalr" (storedOutputs .instr_jalr)
  output "decoded_rd" (storedOutputs .decoded_rd)
  output "decoded_rs1" (storedOutputs .decoded_rs1)
  output "decoded_rs2" (storedOutputs .decoded_rs2)
  output "decoded_imm_j" (storedOutputs .decoded_imm_j)
  output "compressed_instr" (storedOutputs .compressed_instr)
  output "is_beq_bne_blt_bge_bltu_bgeu" branch
  output "is_lb_lh_lw_lbu_lhu" (storedOutputs .is_lb_lh_lw_lbu_lhu)
  output "is_sb_sh_sw" (storedOutputs .is_sb_sh_sw)
  output "is_alu_reg_imm" (storedOutputs .is_alu_reg_imm)
  output "is_alu_reg_reg" (storedOutputs .is_alu_reg_reg)

noncomputable def description : Description := build construction

end Description

/- The expanded typed structure lives under `Internal`; this description is
the reader-facing hardware definition. -/

/-! ## Placement -/

abbrev InputNets :=
  (input : ports.inputs.Label) →
    Authoring.CircuitDescription.Net (ports.inputs.signalType input)

abbrev OutputNets :=
  (output : ports.outputs.Label) →
    Authoring.CircuitDescription.Net (ports.outputs.signalType output)

/-- Place the capture stage using the next conventional indexed name. -/
noncomputable def place (inputs : InputNets) :
    Authoring.CircuitDescription.Builder OutputNets :=
  Authoring.CircuitDescription.placeIndexed "decoder_capture_stage" design inputs

/-- Place the capture stage under an explicit structural instance name. -/
noncomputable def placeNamed (name : Naming.SourceName) (inputs : InputNets) :
    Authoring.CircuitDescription.Builder OutputNets :=
  Authoring.CircuitDescription.placeNamed name design inputs

attribute [circuit_description] place placeNamed

/-! ## Behavioral contract -/

structure Inputs where
  resetn : Bool
  mem_do_rinst : Bool
  mem_done : Bool
  mem_rdata_latched : Word

def valuesOf (inputs : inputMap.Values) : Inputs where
  resetn := inputs .resetn
  mem_do_rinst := inputs .mem_do_rinst
  mem_done := inputs .mem_done
  mem_rdata_latched := inputs .mem_rdata_latched

def opcodeBits (word : Word) : Fin 7 → Bool :=
  Silean.Modules.VectorSlice.slice (prefixWidth := 0) (width := 7) (suffixWidth := 25) word

def funct3Bits (word : Word) : Fin 3 → Bool :=
  Silean.Modules.VectorSlice.slice (prefixWidth := 12) (width := 3) (suffixWidth := 17) word

def addressBits (low : Nat) (suffix : Nat)
    (word : Fin (low + 5 + suffix) → Bool) : RegisterAddress :=
  Silean.Modules.VectorSlice.slice (prefixWidth := low) (width := 5) (suffixWidth := suffix) word

def matchesBits (width value : Nat) (actual : Fin width → Bool) : Bool :=
  (Silean.SignalType.vector width .bit).equal actual (bits width value)

def immediateJBits (word : Word) : Word :=
  Silean.Modules.VectorLayout.apply immediateJLayout word

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

def outputRule : Silean.Contracts.Cycle.CycleOutputRule ports stateMap where
  readsInputs := .empty inputMap
  writesOutputs := .all stateMap
  target _ state := state

def stateRule : Silean.Contracts.Cycle.CycleStateRule ports stateMap where
  readsInputs := .all inputMap
  target inputs state := nextState (valuesOf inputs) state

@[simp] theorem outputRule_writes (output : Output) :
    output ∈ outputRule.writesOutputs.labels := by
  change output ∈ (Silean.SignalGroup.all stateMap).labels
  rw [Silean.SignalGroup.all_labels]
  exact (stateMap.labels.locate output).mem

@[simp] theorem stateRule_reads (input : Input) :
    input ∈ stateRule.readsInputs.labels := by
  change input ∈ (Silean.SignalGroup.all inputMap).labels
  rw [Silean.SignalGroup.all_labels]
  exact (inputMap.labels.locate input).mem

module_cycle_contract cycleContract for ports where
  state := stateMap
  output_rule outputs := outputRule
  state_rule := stateRule

@[simp] theorem outputRule_holds_iff
    (inputs : ports.inputs.Values) (state : stateMap.Values)
    (outputs : ports.outputs.Values) :
    outputRule.Holds inputs state outputs ↔ outputs = state := by
  simp [outputRule, Silean.Contracts.Cycle.CycleOutputRule.Holds]

end PicoRV.Decoder.CaptureStage
