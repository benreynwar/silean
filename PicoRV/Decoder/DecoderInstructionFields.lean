import PicoRV.Decoder.DecoderInstructionMatch
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModuleDesign
import Silean.Modules.EqualsConstant.EqualsConstant
import Silean.Modules.VectorLayout.VectorLayout
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.Constant

namespace PicoRV.Decoder.InstructionFields

open Silean
open Silean.Authoring
open InstructionMatch

/-! Shared comparisons used by the instruction matcher. This child extracts the
RISC-V encoding fields once and exposes the comparisons consumed by the exact
instruction predicates. -/

module_ports ports where
  input word : .vector 32 .bit,
  output funct3_0 : .bit,
  output funct3_1 : .bit,
  output funct3_2 : .bit,
  output funct3_3 : .bit,
  output funct3_4 : .bit,
  output funct3_5 : .bit,
  output funct3_6 : .bit,
  output funct3_7 : .bit,
  output funct7_zero : .bit,
  output funct7_alternate : .bit,
  output opcode_system : .bit,
  output opcode_fence : .bit,
  output system_middle_zero : .bit,
  output system_outer_zero : .bit,
  output true_value : .bit

def outputValues (word : Word) : ports.outputs.Values
  | .funct3_0 => decide (funct3 word = 0)
  | .funct3_1 => decide (funct3 word = 1)
  | .funct3_2 => decide (funct3 word = 2)
  | .funct3_3 => decide (funct3 word = 3)
  | .funct3_4 => decide (funct3 word = 4)
  | .funct3_5 => decide (funct3 word = 5)
  | .funct3_6 => decide (funct3 word = 6)
  | .funct3_7 => decide (funct3 word = 7)
  | .funct7_zero => decide (funct7 word = 0)
  | .funct7_alternate => decide (funct7 word = 0x20)
  | .opcode_system => decide (opcode word = 0x73)
  | .opcode_fence => decide (opcode word = 0x0f)
  | .system_middle_zero => decide (field word 21 11 = 0)
  | .system_outer_zero => decide (field word 7 13 = 0)
  | .true_value => true

def outputRule : Silean.Contracts.Cycle.CycleOutputRule ports emptySignalMap where
  readsInputs := .all inputMap
  writesOutputs := .all outputMap
  target inputs _ := outputValues (inputs .word)

module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule apply := outputRule
  state_rule := Silean.Contracts.Cycle.CycleStateRule.empty _

@[simp] theorem output_signalType (output : Output) :
    outputMap.signalType output = .bit := by
  cases output <;> rfl

@[simp] theorem outputRule_holds_iff
    (inputs : ports.inputs.Values) (state : emptySignalMap.Values)
    (outputs : ports.outputs.Values) :
    outputRule.Holds inputs state outputs ↔ outputs = outputValues (inputs .word) := by
  simp [Silean.Contracts.Cycle.CycleOutputRule.Holds, outputRule]

def funct3Layout (index : Fin 3) : Silean.Modules.VectorLayout.BitSource 32 :=
  .input ⟨index.val + 12, by omega⟩

def funct7Layout (index : Fin 7) : Silean.Modules.VectorLayout.BitSource 32 :=
  .input ⟨index.val + 25, by omega⟩

def opcodeLayout (index : Fin 7) : Silean.Modules.VectorLayout.BitSource 32 :=
  .input ⟨index.val, by omega⟩

def systemMiddleLayout (index : Fin 11) : Silean.Modules.VectorLayout.BitSource 32 :=
  .input ⟨index.val + 21, by omega⟩

def systemOuterLayout (index : Fin 13) : Silean.Modules.VectorLayout.BitSource 32 :=
  .input ⟨index.val + 7, by omega⟩

module_design Structure (name := "PicoRVDecoderInstructionFields") where
  boundary (ports) (naming := Naming.ports)
  instances {
    funct3Bits := Silean.Modules.VectorLayout.design 32 3 funct3Layout,
    funct7Bits := Silean.Modules.VectorLayout.design 32 7 funct7Layout,
    opcodeBits := Silean.Modules.VectorLayout.design 32 7 opcodeLayout,
    systemMiddleBits := Silean.Modules.VectorLayout.design 32 11 systemMiddleLayout,
    systemOuterBits := Silean.Modules.VectorLayout.design 32 13 systemOuterLayout,
    funct3Equals (code : Fin 8 in Silean.Enumeration.fin 8)
      (name := s!"equals_funct3_{code.val}") :=
        Silean.Modules.EqualsConstant.design (.vector 3 .bit) (Silean.BitVector.ofNat 3 code.val),
    funct7Zero := Silean.Modules.EqualsConstant.design (.vector 7 .bit) (Silean.BitVector.ofNat 7 0),
    funct7Alternate := Silean.Modules.EqualsConstant.design (.vector 7 .bit)
      (Silean.BitVector.ofNat 7 0x20),
    opcodeSystem := Silean.Modules.EqualsConstant.design (.vector 7 .bit)
      (Silean.BitVector.ofNat 7 0x73),
    opcodeFence := Silean.Modules.EqualsConstant.design (.vector 7 .bit)
      (Silean.BitVector.ofNat 7 0x0f),
    systemMiddleZero := Silean.Modules.EqualsConstant.design (.vector 11 .bit)
      (Silean.BitVector.ofNat 11 0),
    systemOuterZero := Silean.Modules.EqualsConstant.design (.vector 13 .bit)
      (Silean.BitVector.ofNat 13 0),
    trueValue := Silean.Primitives.constantDesign true }
  wiring {
  outputs {
    .funct3_0 := funct3Equals(0)[.result],
    .funct3_1 := funct3Equals(1)[.result],
    .funct3_2 := funct3Equals(2)[.result],
    .funct3_3 := funct3Equals(3)[.result],
    .funct3_4 := funct3Equals(4)[.result],
    .funct3_5 := funct3Equals(5)[.result],
    .funct3_6 := funct3Equals(6)[.result],
    .funct3_7 := funct3Equals(7)[.result],
    .funct7_zero := funct7Zero.result,
    .funct7_alternate := funct7Alternate.result,
    .opcode_system := opcodeSystem.result,
    .opcode_fence := opcodeFence.result,
    .system_middle_zero := systemMiddleZero.result,
    .system_outer_zero := systemOuterZero.result,
    .true_value := trueValue.output }
  instance (.funct3Bits) { .input := input.word }
  instance (.funct7Bits) { .input := input.word }
  instance (.opcodeBits) { .input := input.word }
  instance (.systemMiddleBits) { .input := input.word }
  instance (.systemOuterBits) { .input := input.word }
  instance (.funct3Equals _) { .value := funct3Bits.output }
  instance (.funct7Zero) { .value := funct7Bits.output }
  instance (.funct7Alternate) { .value := funct7Bits.output }
  instance (.opcodeSystem) { .value := opcodeBits.output }
  instance (.opcodeFence) { .value := opcodeBits.output }
  instance (.systemMiddleZero) { .value := systemMiddleBits.output }
  instance (.systemOuterZero) { .value := systemOuterBits.output }
  instance (.trueValue) {}
  }

end PicoRV.Decoder.InstructionFields
