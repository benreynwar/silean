import PicoRV.Decoder.DecoderInstructionFields
import Silean.Authoring.ModuleDesign
import Silean.Modules.EqualsConstant.EqualsConstantDerived
import Silean.Modules.VectorLayout.VectorLayoutDerived
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.Constant

namespace PicoRV.Decoder.InstructionFields.Structure

open Silean

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

end PicoRV.Decoder.InstructionFields.Structure

namespace PicoRV.Decoder.InstructionFields

open Silean
open Silean.Authoring

module_design Structure (name := "PicoRVDecoderInstructionFields") where
  boundary (ports) (naming := Naming.ports)
  instances {
    funct3Bits := Silean.Modules.VectorLayout.design 32 3 Structure.funct3Layout,
    funct7Bits := Silean.Modules.VectorLayout.design 32 7 Structure.funct7Layout,
    opcodeBits := Silean.Modules.VectorLayout.design 32 7 Structure.opcodeLayout,
    systemMiddleBits := Silean.Modules.VectorLayout.design 32 11 Structure.systemMiddleLayout,
    systemOuterBits := Silean.Modules.VectorLayout.design 32 13 Structure.systemOuterLayout,
    funct3Equals (code : Fin 8 in Silean.Enumeration.fin 8)
      (name := s!"equals_funct3_{code.val}") :=
        Silean.Modules.EqualsConstant.design (.vector 3 .bit)
          (Silean.BitVector.ofNat 3 code.val),
    funct7Zero := Silean.Modules.EqualsConstant.design (.vector 7 .bit)
      (Silean.BitVector.ofNat 7 0),
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
