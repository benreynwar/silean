import PicoRV.Decoder.DecoderTypes
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.CircuitDescription
import Silean.Authoring.ModulePorts
import Silean.Foundation.SignalLayout
import Silean.Contracts.Cycle.CycleContract
import Silean.Contracts.Cycle.CycleEvaluation
import PicoRV.Authoring.CircuitLogic

namespace PicoRV.Decoder.Immediate

open Silean
open Silean.Authoring
open PicoRV.Decoder

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

def immediateILayout (index : Fin 32) : Silean.Modules.VectorLayout.BitSource 32 :=
  if _low : index.val < 12 then .input ⟨index.val + 20, by omega⟩
  else .input ⟨31, by omega⟩

def immediateULayout (index : Fin 32) : Silean.Modules.VectorLayout.BitSource 32 :=
  if _low : index.val < 12 then .constant false else .input index

def immediateSLayout (index : Fin 32) : Silean.Modules.VectorLayout.BitSource 32 :=
  if _low : index.val < 5 then .input ⟨index.val + 7, by omega⟩
  else if _middle : index.val < 12 then .input ⟨index.val + 20, by omega⟩
  else .input ⟨31, by omega⟩

def immediateBLayout (index : Fin 32) : Silean.Modules.VectorLayout.BitSource 32 :=
  if _zero : index.val = 0 then .constant false
  else if _low : index.val < 5 then .input ⟨index.val + 7, by omega⟩
  else if _middle : index.val < 11 then .input ⟨index.val + 20, by omega⟩
  else if _eleven : index.val = 11 then .input ⟨7, by omega⟩
  else .input ⟨31, by omega⟩

/-! Combinational immediate selection for the configured PicoRV32 decoder.
The Lean behavior is naturally an `Option Word`: no selected instruction class
means that the resolve stage must retain its existing immediate. The hardware
boundary exposes this as `valid` plus `value`; the value is zero when invalid
and must not be consumed. Selection order matches the source `case (1'b1)`. -/

/-! ## Authored hardware

Four vector layouts construct the immediates encoded in the instruction word.
The OR expressions name the instruction classes; the mux chain is written in
the source decoder's priority order, from the lowest-priority S immediate to
the highest-priority J immediate. -/

open Silean.Authoring.CircuitDescription
open PicoRV.Authoring
open scoped Silean.Authoring
open ports

noncomputable def construction : ModuleBuilder ports Unit := do
  let word ← input .word
  let decodedImmJ ← input .decoded_imm_j
  let instrJal ← input .instr_jal
  let instrLui ← input .instr_lui
  let instrAuipc ← input .instr_auipc
  let instrJalr ← input .instr_jalr
  let isLoad ← input .is_lb_lh_lw_lbu_lhu
  let isAluImmediate ← input .is_alu_reg_imm
  let isBranch ← input .is_beq_bne_blt_bge_bltu_bgeu
  let isStore ← input .is_sb_sh_sw

  let immediateI ← Silean.Modules.VectorLayout.place immediateILayout word
  let immediateU ← Silean.Modules.VectorLayout.place immediateULayout word
  let immediateS ← Silean.Modules.VectorLayout.place immediateSLayout word
  let immediateB ← Silean.Modules.VectorLayout.place immediateBLayout word
  let uSelected ← instrLui ||| instrAuipc
  let iSelected ← (← instrJalr ||| isLoad) ||| isAluImmediate
  let lowerValid ← isBranch ||| isStore
  let valid ← instrJal ||| (← uSelected ||| (← iSelected ||| lowerValid))
  let zero ← constant (.vector 32 .bit) (fun _ => false)
  let value ← mux instrJal
    (← mux uSelected
      (← mux iSelected
        (← mux isBranch
          (← mux isStore zero immediateS)
          immediateB)
        immediateI)
      immediateU)
    decodedImmJ

  output .valid valid
  output .value value

noncomputable def description : Description :=
  ModuleBuilder.build Naming.ports construction

/-! ## Behavioral contract -/

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

def outputRule : Silean.Contracts.Cycle.CycleOutputRule ports emptySignalMap where
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
  change input ∈ (Silean.SignalGroup.all inputMap).labels
  rw [Silean.SignalGroup.all_labels]
  exact (inputMap.labels.locate input).mem

@[simp] theorem outputRule_writes (output : Output) :
    output ∈ outputRule.writesOutputs.labels := by
  change output ∈ (Silean.SignalGroup.all outputMap).labels
  rw [Silean.SignalGroup.all_labels]
  exact (outputMap.labels.locate output).mem

@[simp] theorem outputRule_holds_iff
    (inputs : ports.inputs.Values) (state : emptySignalMap.Values)
    (outputs : ports.outputs.Values) :
    outputRule.Holds inputs state outputs ↔
      outputs = outputValues (valuesOf inputs) := by
  simp [Silean.Contracts.Cycle.CycleOutputRule.Holds, outputRule]

theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs = outputValues (valuesOf step.inputs) :=
  (outputRule_holds_iff step.inputs step.currentState step.outputs).mp
    (allowed.1 .apply)

end PicoRV.Decoder.Immediate
