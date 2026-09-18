import PicoRV.Memory.MemoryCombinationalContracts
import Silean.Authoring.ModuleDesign
import Silean.Modules.EqualsConstant.EqualsConstant
import Silean.Modules.Mux.Mux
import Silean.Modules.VectorLayout.VectorLayout
import Silean.Modules.VectorSlice.VectorSlice

namespace PicoRV.Memory

open Silean
open Silean.Authoring

def ReadFormatting.halfLayout (high : Bool) (index : Fin 32) :
    Silean.Modules.VectorLayout.BitSource 32 :=
  if low : index.val < 16 then
    .input ⟨index.val + if high then 16 else 0, by
      cases high <;> simp <;> omega⟩
  else
    .constant false

def ReadFormatting.byteLayout (lane : Fin 4) (index : Fin 32) :
    Silean.Modules.VectorLayout.BitSource 32 :=
  if low : index.val < 8 then
    .input ⟨index.val + 8 * lane.val, by omega⟩
  else
    .constant false

def ReadFormatting.byte0Layout := ReadFormatting.byteLayout ⟨0, by decide⟩
def ReadFormatting.byte1Layout := ReadFormatting.byteLayout ⟨1, by decide⟩
def ReadFormatting.byte2Layout := ReadFormatting.byteLayout ⟨2, by decide⟩
def ReadFormatting.byte3Layout := ReadFormatting.byteLayout ⟨3, by decide⟩

/-! Select the addressed byte or halfword and zero-extend it. The final
word-size muxes deliberately make encodings 0 and 3 return the full word,
matching the configured Verilog's `full_case` totalization in the contract. -/
module_design ReadFormatting (name := "picorv32_memory_read_formatting") where
  boundary (ReadFormatting.ports) (naming := ReadFormatting.Naming.ports)
  instances {
    lowBit := Silean.Modules.VectorSlice.design .bit 0 1 31,
    highBit := Silean.Modules.VectorSlice.design .bit 1 1 30,
    lowLane := Silean.Modules.EqualsConstant.design (.vector 1 .bit) (fun _ => true),
    highLane := Silean.Modules.EqualsConstant.design (.vector 1 .bit) (fun _ => true),
    halfLow := Silean.Modules.VectorLayout.design 32 32
      (ReadFormatting.halfLayout false),
    halfHigh := Silean.Modules.VectorLayout.design 32 32
      (ReadFormatting.halfLayout true),
    byte0 := Silean.Modules.VectorLayout.design 32 32
      ReadFormatting.byte0Layout,
    byte1 := Silean.Modules.VectorLayout.design 32 32
      ReadFormatting.byte1Layout,
    byte2 := Silean.Modules.VectorLayout.design 32 32
      ReadFormatting.byte2Layout,
    byte3 := Silean.Modules.VectorLayout.design 32 32
      ReadFormatting.byte3Layout,
    halfValue := Silean.Modules.Mux.design (.vector 32 .bit),
    lowByteValue := Silean.Modules.Mux.design (.vector 32 .bit),
    highByteValue := Silean.Modules.Mux.design (.vector 32 .bit),
    byteValue := Silean.Modules.Mux.design (.vector 32 .bit),
    halfWordsize := Silean.Modules.EqualsConstant.design (.vector 2 .bit) (stateOfNat 1),
    byteWordsize := Silean.Modules.EqualsConstant.design (.vector 2 .bit) (stateOfNat 2),
    selectHalf := Silean.Modules.Mux.design (.vector 32 .bit),
    selectByte := Silean.Modules.Mux.design (.vector 32 .bit) }
  wiring {
  outputs { .mem_rdata_word := selectByte.result }
  instance (.lowBit) { .value := input.reg_op1 }
  instance (.highBit) { .value := input.reg_op1 }
  instance (.lowLane) { .value := lowBit.result }
  instance (.highLane) { .value := highBit.result }
  instance (.halfLow) { .input := input.mem_rdata }
  instance (.halfHigh) { .input := input.mem_rdata }
  instance (.byte0) { .input := input.mem_rdata }
  instance (.byte1) { .input := input.mem_rdata }
  instance (.byte2) { .input := input.mem_rdata }
  instance (.byte3) { .input := input.mem_rdata }
  instance (.halfValue) {
    .select := highLane.result,
    .whenFalse := halfLow.output,
    .whenTrue := halfHigh.output }
  instance (.lowByteValue) {
    .select := lowLane.result,
    .whenFalse := byte0.output,
    .whenTrue := byte1.output }
  instance (.highByteValue) {
    .select := lowLane.result,
    .whenFalse := byte2.output,
    .whenTrue := byte3.output }
  instance (.byteValue) {
    .select := highLane.result,
    .whenFalse := lowByteValue.result,
    .whenTrue := highByteValue.result }
  instance (.halfWordsize) { .value := input.mem_wordsize }
  instance (.byteWordsize) { .value := input.mem_wordsize }
  instance (.selectHalf) {
    .select := halfWordsize.result,
    .whenFalse := input.mem_rdata,
    .whenTrue := halfValue.result }
  instance (.selectByte) {
    .select := byteWordsize.result,
    .whenFalse := selectHalf.result,
    .whenTrue := byteValue.result }
  }

end PicoRV.Memory
