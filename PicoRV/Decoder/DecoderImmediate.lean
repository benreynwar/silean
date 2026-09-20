import PicoRV.Decoder.DecoderTypes
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.CircuitDescription
import Silean.Authoring.ModulePorts
import Silean.Foundation.SignalLayout
import Silean.Contracts.Cycle.CycleContract
import Silean.Contracts.Cycle.CycleEvaluation
import PicoRV.Authoring.CircuitLogic
import PicoRV.Decoder.Internal.DecoderImmediateStructure

namespace PicoRV.Decoder.Immediate

open Silean
open Silean.Authoring
open PicoRV.Decoder

/-! Combinational immediate selection for the configured PicoRV32 decoder.
The Lean behavior is naturally an `Option Word`: no selected instruction class
means that the resolve stage must retain its existing immediate. The hardware
boundary exposes this as `valid` plus `value`; the value is zero when invalid
and must not be consumed. Selection order matches the source `case (1'b1)`. -/

/-! ## Immediate layouts

These layouts are the concrete wiring for the four immediates decoded directly
from the instruction word. The lemmas below connect that bit-level wiring to
the arithmetic definitions in `DecoderTypes`, keeping those readable
definitions as the behavioral specification. -/

private theorem field_testBit (word : Word) (low width index : Nat)
    (inField : index < width) (inWord : index + low < 32) :
    (field word low width).testBit index = word ⟨index + low, inWord⟩ := by
  simp only [field, Nat.testBit_mod_two_pow, inField, decide_true,
    Bool.true_and, Nat.testBit_div_two_pow]
  exact Silean.BitVector.testBit_toNat 32 word ⟨index + low, inWord⟩

private theorem signExtend12_bit (value : Nat) (bound : value < 2 ^ 12)
    (index : Fin 32) :
    signExtend 12 value index =
      if index.val < 12 then value.testBit index.val else value.testBit 11 := by
  simp only [signExtend, wordOfNat]
  by_cases sign : value < 2 ^ (12 - 1)
  · simp only [sign, ↓reduceIte]
    by_cases low : index.val < 12
    · simp [low]
    · simp only [low, ↓reduceIte]
      have indexBound : value < 2 ^ index.val :=
        Nat.lt_of_lt_of_le sign (Nat.pow_le_pow_right (by decide) (by omega))
      rw [Nat.testBit_lt_two_pow indexBound,
        Nat.testBit_lt_two_pow (by simpa using sign)]
  · simp only [sign, ↓reduceIte]
    have extended : value + 2 ^ 32 - 2 ^ 12 =
        2 ^ 12 * (2 ^ 20 - 1) + value := by
      simp [Nat.pow_succ]
      exact Nat.add_comm _ _
    rw [extended, Nat.testBit_two_pow_mul_add (2 ^ 20 - 1) bound]
    by_cases low : index.val < 12
    · simp [low]
    · simp only [low, ↓reduceIte]
      have signBit : value.testBit 11 = true := by
        apply Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt
        · simp [Nat.pow_succ] at sign ⊢
          omega
        · simp [Nat.pow_succ] at bound ⊢
          omega
      rw [Nat.testBit_two_pow_sub_one]
      simp [show index.val - 12 < 20 by omega, signBit]

private theorem signExtend13_bit (value : Nat) (bound : value < 2 ^ 13)
    (index : Fin 32) :
    signExtend 13 value index =
      if index.val < 13 then value.testBit index.val else value.testBit 12 := by
  simp only [signExtend, wordOfNat]
  by_cases sign : value < 2 ^ (13 - 1)
  · simp only [sign, ↓reduceIte]
    by_cases low : index.val < 13
    · simp [low]
    · simp only [low, ↓reduceIte]
      have indexBound : value < 2 ^ index.val :=
        Nat.lt_of_lt_of_le sign (Nat.pow_le_pow_right (by decide) (by omega))
      rw [Nat.testBit_lt_two_pow indexBound,
        Nat.testBit_lt_two_pow (by simpa using sign)]
  · simp only [sign, ↓reduceIte]
    have extended : value + 2 ^ 32 - 2 ^ 13 =
        2 ^ 13 * (2 ^ 19 - 1) + value := by
      simp [Nat.pow_succ]
      exact Nat.add_comm _ _
    rw [extended, Nat.testBit_two_pow_mul_add (2 ^ 19 - 1) bound]
    by_cases low : index.val < 13
    · simp [low]
    · simp only [low, ↓reduceIte]
      have signBit : value.testBit 12 = true := by
        apply Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt
        · simp [Nat.pow_succ] at sign ⊢
          omega
        · simp [Nat.pow_succ] at bound ⊢
          omega
      rw [Nat.testBit_two_pow_sub_one]
      simp [show index.val - 13 < 19 by omega, signBit]

theorem immediateI_layout (word : Word) :
    Silean.Modules.VectorLayout.apply immediateILayout word = immediateI word := by
  funext index
  let value := field word 20 12
  have valueBound : value < 2 ^ 12 := Nat.mod_lt _ (by decide)
  change Silean.Modules.VectorLayout.apply immediateILayout word index =
    signExtend 12 value index
  rw [signExtend12_bit value valueBound]
  by_cases low : index.val < 12
  · simp only [Silean.Modules.VectorLayout.apply, immediateILayout, low, dif_pos,
      value, ↓reduceIte]
    exact (field_testBit word 20 12 index.val low (by omega)).symm
  · simp only [Silean.Modules.VectorLayout.apply, immediateILayout, low,
      value, ↓reduceIte]
    exact (field_testBit word 20 12 11 (by omega) (by omega)).symm

theorem immediateU_layout (word : Word) :
    Silean.Modules.VectorLayout.apply immediateULayout word = immediateU word := by
  funext index
  by_cases low : index.val < 12
  · simp only [Silean.Modules.VectorLayout.apply, immediateULayout, low, dif_pos,
      immediateU, wordOfNat]
    rw [Nat.testBit_mul_two_pow]
    simp [show ¬12 ≤ index.val by omega]
  · simp only [Silean.Modules.VectorLayout.apply, immediateULayout, low,
      immediateU, wordOfNat]
    rw [Nat.testBit_mul_two_pow]
    simp only [show 12 ≤ index.val by omega, decide_true, Bool.true_and]
    have inField : index.val - 12 < 20 := by omega
    rw [field_testBit word 12 20 (index.val - 12) inField (by omega)]
    apply congrArg word
    apply Fin.ext
    simp
    omega

theorem immediateS_layout (word : Word) :
    Silean.Modules.VectorLayout.apply immediateSLayout word = immediateS word := by
  funext index
  let lowField := field word 7 5
  let highField := field word 25 7
  let value := lowField + highField * 2 ^ 5
  have lowBound : lowField < 2 ^ 5 := Nat.mod_lt _ (by decide)
  have highBound : highField < 2 ^ 7 := Nat.mod_lt _ (by decide)
  have valueBound : value < 2 ^ 12 := by
    simp [value, Nat.pow_succ] at lowBound highBound ⊢
    omega
  change Silean.Modules.VectorLayout.apply immediateSLayout word index =
    signExtend 12 value index
  rw [signExtend12_bit value valueBound]
  have valueBits : value.testBit index.val =
      if index.val < 5 then lowField.testBit index.val
      else highField.testBit (index.val - 5) := by
    rw [show value = 2 ^ 5 * highField + lowField by
      simp [value, Nat.mul_comm, Nat.add_comm]]
    exact Nat.testBit_two_pow_mul_add highField lowBound index.val
  by_cases low : index.val < 5
  · simp only [Silean.Modules.VectorLayout.apply, immediateSLayout, low, dif_pos,
      show index.val < 12 by omega, ↓reduceIte]
    rw [valueBits, if_pos low]
    exact (field_testBit word 7 5 index.val low (by omega)).symm
  · by_cases middle : index.val < 12
    · simp [Silean.Modules.VectorLayout.apply, immediateSLayout, low, middle]
      rw [valueBits, if_neg low]
      rw [field_testBit word 25 7 (index.val - 5) (by omega) (by omega)]
      apply congrArg word
      apply Fin.ext
      simp
      omega
    · simp [Silean.Modules.VectorLayout.apply, immediateSLayout, low, middle]
      rw [show value.testBit 11 = highField.testBit 6 by
        rw [show value = 2 ^ 5 * highField + lowField by
          simp [value, Nat.mul_comm, Nat.add_comm]]
        rw [Nat.testBit_two_pow_mul_add highField lowBound]
        simp]
      exact (field_testBit word 25 7 6 (by omega) (by omega)).symm

theorem immediateB_layout (word : Word) :
    Silean.Modules.VectorLayout.apply immediateBLayout word = immediateB word := by
  funext index
  let field8 := field word 8 4
  let field25 := field word 25 6
  let field7 := field word 7 1
  let field31 := field word 31 1
  let low1 := field8 * 2
  let low2 := low1 + field25 * 2 ^ 5
  let low3 := low2 + field7 * 2 ^ 11
  let value := low3 + field31 * 2 ^ 12
  have field8Bound : field8 < 2 ^ 4 := Nat.mod_lt _ (by decide)
  have field25Bound : field25 < 2 ^ 6 := Nat.mod_lt _ (by decide)
  have field7Bound : field7 < 2 ^ 1 := Nat.mod_lt _ (by decide)
  have field31Bound : field31 < 2 ^ 1 := Nat.mod_lt _ (by decide)
  have low1Bound : low1 < 2 ^ 5 := by
    simp [low1, Nat.pow_succ] at field8Bound ⊢
    omega
  have low2Bound : low2 < 2 ^ 11 := by
    simp [low2, Nat.pow_succ] at field25Bound low1Bound ⊢
    omega
  have low3Bound : low3 < 2 ^ 12 := by
    simp [low3, Nat.pow_succ] at field7Bound low2Bound ⊢
    omega
  have valueBound : value < 2 ^ 13 := by
    simp [value, Nat.pow_succ] at field31Bound low3Bound ⊢
    omega
  have valueTop (bit : Nat) : value.testBit bit =
      if bit < 12 then low3.testBit bit else field31.testBit (bit - 12) := by
    rw [show value = 2 ^ 12 * field31 + low3 by
      simp [value, Nat.mul_comm, Nat.add_comm]]
    exact Nat.testBit_two_pow_mul_add field31 low3Bound bit
  have low3Bits (bit : Nat) : low3.testBit bit =
      if bit < 11 then low2.testBit bit else field7.testBit (bit - 11) := by
    rw [show low3 = 2 ^ 11 * field7 + low2 by
      simp [low3, Nat.mul_comm, Nat.add_comm]]
    exact Nat.testBit_two_pow_mul_add field7 low2Bound bit
  have low2Bits (bit : Nat) : low2.testBit bit =
      if bit < 5 then low1.testBit bit else field25.testBit (bit - 5) := by
    rw [show low2 = 2 ^ 5 * field25 + low1 by
      simp [low2, Nat.mul_comm, Nat.add_comm]]
    exact Nat.testBit_two_pow_mul_add field25 low1Bound bit
  have low1Bits (bit : Nat) : low1.testBit bit =
      (decide (1 ≤ bit) && field8.testBit (bit - 1)) := by
    simpa [low1, Nat.mul_comm] using Nat.testBit_mul_two_pow field8 bit 1
  change Silean.Modules.VectorLayout.apply immediateBLayout word index =
    signExtend 13 value index
  rw [signExtend13_bit value valueBound]
  by_cases zero : index.val = 0
  · have indexEq : index = ⟨0, by omega⟩ := Fin.ext zero
    rw [indexEq]
    simp [Silean.Modules.VectorLayout.apply, immediateBLayout, valueTop,
      low3Bits, low2Bits, low1Bits]
  · by_cases low : index.val < 5
    · have positive : 1 ≤ index.val := by omega
      simp [Silean.Modules.VectorLayout.apply, immediateBLayout, zero, low,
        show index.val < 11 by omega, show index.val < 12 by omega,
        show index.val < 13 by omega, valueTop, low3Bits, low2Bits, low1Bits,
        positive]
      rw [field_testBit word 8 4 (index.val - 1) (by omega) (by omega)]
      apply congrArg word
      apply Fin.ext
      simp
      omega
    · by_cases middle : index.val < 11
      · simp [Silean.Modules.VectorLayout.apply, immediateBLayout, zero, low,
          middle, show index.val < 12 by omega, show index.val < 13 by omega,
          valueTop, low3Bits, low2Bits]
        rw [field_testBit word 25 6 (index.val - 5) (by omega) (by omega)]
        apply congrArg word
        apply Fin.ext
        simp
        omega
      · by_cases eleven : index.val = 11
        · have indexEq : index = ⟨11, by omega⟩ := Fin.ext eleven
          rw [indexEq]
          simp [Silean.Modules.VectorLayout.apply, immediateBLayout, valueTop,
            low3Bits]
          simpa [field7, Nat.testBit_zero] using
            (field_testBit word 7 1 0 (by omega) (by omega)).symm
        · by_cases twelve : index.val < 13
          · have indexTwelve : index.val = 12 := by omega
            simp [Silean.Modules.VectorLayout.apply, immediateBLayout, valueTop,
              indexTwelve]
            simpa [field31, Nat.testBit_zero] using
              (field_testBit word 31 1 0 (by omega) (by omega)).symm
          · simp [Silean.Modules.VectorLayout.apply, immediateBLayout, zero, low,
              middle, eleven, twelve, valueTop]
            simpa [field31, Nat.testBit_zero] using
              (field_testBit word 31 1 0 (by omega) (by omega)).symm

/-! ## Authored hardware

Four vector layouts construct the immediates encoded in the instruction word.
The OR expressions name the instruction classes; the mux chain is written in
the source decoder's priority order, from the lowest-priority S immediate to
the highest-priority J immediate. -/

namespace Description

open Silean.Authoring.CircuitDescription
open PicoRV.Authoring
open scoped Silean.Authoring

noncomputable def construction : Builder Unit := do
  let word ← input "word" (.vector 32 .bit)
  let decodedImmJ ← input "decoded_imm_j" (.vector 32 .bit)
  let instrJal ← input "instr_jal" .bit
  let instrLui ← input "instr_lui" .bit
  let instrAuipc ← input "instr_auipc" .bit
  let instrJalr ← input "instr_jalr" .bit
  let isLoad ← input "is_lb_lh_lw_lbu_lhu" .bit
  let isAluImmediate ← input "is_alu_reg_imm" .bit
  let isBranch ← input "is_beq_bne_blt_bge_bltu_bgeu" .bit
  let isStore ← input "is_sb_sh_sw" .bit

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

  output "valid" valid
  output "value" value

noncomputable def description : Description := build construction

end Description

/-! ## Placement -/

abbrev InputNets :=
  (input : ports.inputs.Label) →
    Authoring.CircuitDescription.Net (ports.inputs.signalType input)

structure PlacedOutputs where
  valid : Authoring.CircuitDescription.Net .bit
  value : Authoring.CircuitDescription.Net (.vector 32 .bit)

noncomputable def place (inputs : InputNets) :
    Authoring.CircuitDescription.Builder PlacedOutputs := do
  let child ← Authoring.CircuitDescription.placeIndexed
    "decoder_immediate" design inputs
  pure { valid := child .valid, value := child .value }

noncomputable def placeNamed (name : Naming.SourceName) (inputs : InputNets) :
    Authoring.CircuitDescription.Builder PlacedOutputs := do
  let child ← Authoring.CircuitDescription.placeNamed name design inputs
  pure { valid := child .valid, value := child .value }

attribute [circuit_description] place placeNamed

end PicoRV.Decoder.Immediate

namespace PicoRV.Decoder.Immediate

open Silean
open Silean.Authoring
open PicoRV.Decoder

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

/-! The following functions state the value computed by the concrete OR and
mux network. Their equivalence lemmas are the semantic bridge used by the
structural certification. -/

def selectedU (inputs : Inputs) : Bool :=
  inputs.instr_lui || inputs.instr_auipc

def selectedI (inputs : Inputs) : Bool :=
  inputs.instr_jalr || inputs.is_lb_lh_lw_lbu_lhu || inputs.is_alu_reg_imm

def structuralValid (inputs : Inputs) : Bool :=
  inputs.instr_jal || (selectedU inputs || (selectedI inputs ||
    (inputs.is_beq_bne_blt_bge_bltu_bgeu || inputs.is_sb_sh_sw)))

def structuralValue (inputs : Inputs) : Word :=
  bif inputs.instr_jal then inputs.decoded_imm_j else
  bif selectedU inputs then Silean.Modules.VectorLayout.apply immediateULayout inputs.word else
  bif selectedI inputs then Silean.Modules.VectorLayout.apply immediateILayout inputs.word else
  bif inputs.is_beq_bne_blt_bge_bltu_bgeu then
    Silean.Modules.VectorLayout.apply immediateBLayout inputs.word else
  bif inputs.is_sb_sh_sw then Silean.Modules.VectorLayout.apply immediateSLayout inputs.word else
    wordOfNat 0

theorem structuralValid_eq (inputs : Inputs) :
    structuralValid inputs = (evaluate inputs).isSome := by
  rcases inputs with ⟨word, decoded, jal, lui, auipc, jalr, load, alu, branch, store⟩
  cases jal <;> cases lui <;> cases auipc <;> cases jalr <;>
    cases load <;> cases alu <;> cases branch <;> cases store <;>
  simp [structuralValid, selectedU, selectedI, evaluate]

theorem structuralValue_eq (inputs : Inputs) :
    structuralValue inputs = (evaluate inputs).getD (wordOfNat 0) := by
  rcases inputs with ⟨word, decoded, jal, lui, auipc, jalr, load, alu, branch, store⟩
  cases jal <;> cases lui <;> cases auipc <;> cases jalr <;>
    cases load <;> cases alu <;> cases branch <;> cases store <;>
  simp [structuralValue, selectedU, selectedI, evaluate,
    immediateU_layout, immediateI_layout, immediateB_layout, immediateS_layout]

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

end PicoRV.Decoder.Immediate
