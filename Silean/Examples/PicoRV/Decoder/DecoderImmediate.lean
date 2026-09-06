import Silean.Examples.PicoRV.Decoder.DecoderTypes
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Foundation.SignalLayout
import Silean.Contracts.Cycle.CycleContract
import Silean.Contracts.Cycle.CycleEvaluation

namespace Silean.Examples.PicoRV.Decoder.Immediate

open Silean
open Silean.Authoring
open Silean.Examples.PicoRV.Decoder

/-! Combinational immediate selection for the configured PicoRV32 decoder.
The Lean behavior is naturally an `Option Word`: no selected instruction class
means that the resolve stage must retain its existing immediate. The hardware
boundary exposes this as `valid` plus `value`; the value is zero when invalid
and must not be consumed. Selection order matches the source `case (1'b1)`. -/

module_ports ports where
  input word : .vector 32 .bit,
  input decoded_imm_j : .vector 32 .bit,
  input instr_jal : .bit,
  input instr_lui : .bit,
  input instr_auipc : .bit,
  input instr_jalr : .bit,
  input is_lb_lh_lw_lbu_lhu : .bit,
  input is_alu_reg_imm : .bit,
  input is_beq_bne_blt_bge_bltu_bgeu : .bit,
  input is_sb_sh_sw : .bit,
  output valid : .bit,
  output value : .vector 32 .bit

structure Inputs where
  word : Word
  decoded_imm_j : Word
  instr_jal : Bool
  instr_lui : Bool
  instr_auipc : Bool
  instr_jalr : Bool
  is_lb_lh_lw_lbu_lhu : Bool
  is_alu_reg_imm : Bool
  is_beq_bne_blt_bge_bltu_bgeu : Bool
  is_sb_sh_sw : Bool

def valuesOf (inputs : inputMap.Values) : Inputs where
  word := inputs .word
  decoded_imm_j := inputs .decoded_imm_j
  instr_jal := inputs .instr_jal
  instr_lui := inputs .instr_lui
  instr_auipc := inputs .instr_auipc
  instr_jalr := inputs .instr_jalr
  is_lb_lh_lw_lbu_lhu := inputs .is_lb_lh_lw_lbu_lhu
  is_alu_reg_imm := inputs .is_alu_reg_imm
  is_beq_bne_blt_bge_bltu_bgeu := inputs .is_beq_bne_blt_bge_bltu_bgeu
  is_sb_sh_sw := inputs .is_sb_sh_sw

def evaluate (inputs : Inputs) : Option Word :=
  if inputs.instr_jal then some inputs.decoded_imm_j
  else if inputs.instr_lui || inputs.instr_auipc then some (immediateU inputs.word)
  else if inputs.instr_jalr || inputs.is_lb_lh_lw_lbu_lhu || inputs.is_alu_reg_imm then
    some (immediateI inputs.word)
  else if inputs.is_beq_bne_blt_bge_bltu_bgeu then some (immediateB inputs.word)
  else if inputs.is_sb_sh_sw then some (immediateS inputs.word)
  else none

def outputValues (inputs : Inputs) : outputMap.Values
  | .valid => (evaluate inputs).isSome
  | .value => (evaluate inputs).getD (wordOfNat 0)

def outputRule : Contracts.Cycle.CycleOutputRule ports emptySignalMap where
  readsInputs := .all inputMap
  writesOutputs := .all outputMap
  target inputs _ := outputValues (valuesOf inputs)

module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule apply := outputRule
  state_rule where
    reads := []
    next := {}

@[simp] theorem outputRule_reads (input : Input) :
    input ∈ outputRule.readsInputs.labels := by
  change input ∈ (SignalGroup.all inputMap).labels
  rw [SignalGroup.all_labels]
  exact (inputMap.labels.locate input).mem

@[simp] theorem outputRule_writes (output : Output) :
    output ∈ outputRule.writesOutputs.labels := by
  change output ∈ (SignalGroup.all outputMap).labels
  rw [SignalGroup.all_labels]
  exact (outputMap.labels.locate output).mem

@[simp] theorem outputRule_holds_iff
    (inputs : ports.inputs.Values) (state : emptySignalMap.Values)
    (outputs : ports.outputs.Values) :
    outputRule.Holds inputs state outputs ↔
      outputs = outputValues (valuesOf inputs) := by
  simp [Contracts.Cycle.CycleOutputRule.Holds, outputRule]

end Silean.Examples.PicoRV.Decoder.Immediate
