import PicoRV.Memory.Internal.MemoryReadFormattingStructure
import PicoRV.Authoring.CircuitLogic
import Silean.Modules.EqualsConstant.EqualsConstant
import Silean.Modules.VectorLayout.VectorLayout
import Silean.Modules.VectorSlice.VectorSlice

namespace PicoRV.Memory

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring

/-! # Memory read formatting

The addressed byte or halfword is selected from the returned memory word and
zero-extended. Final word-size selection deliberately makes encodings 0 and 3
return the full word, matching the configured Verilog's `full_case`
totalization. The expanded typed hierarchy and verification remain under
`Internal/`. -/

namespace ReadFormatting.Description

noncomputable def construction : Builder Unit := do
  let memWordsize ← input "mem_wordsize" (.vector 2 .bit)
  let regOp1 ← input "reg_op1" (.vector 32 .bit)
  let memRdata ← input "mem_rdata" (.vector 32 .bit)

  let lowBit ← Silean.Modules.VectorSlice.place .bit 0 1 31 regOp1
  let highBit ← Silean.Modules.VectorSlice.place .bit 1 1 30 regOp1
  let lowLane ← Silean.Modules.EqualsConstant.place lowBit (fun _ => true)
  let highLane ← Silean.Modules.EqualsConstant.place highBit (fun _ => true)
  let halfLow ← Silean.Modules.VectorLayout.place
    (ReadFormatting.halfLayout false) memRdata
  let halfHigh ← Silean.Modules.VectorLayout.place
    (ReadFormatting.halfLayout true) memRdata
  let byte0 ← Silean.Modules.VectorLayout.place
    ReadFormatting.byte0Layout memRdata
  let byte1 ← Silean.Modules.VectorLayout.place
    ReadFormatting.byte1Layout memRdata
  let byte2 ← Silean.Modules.VectorLayout.place
    ReadFormatting.byte2Layout memRdata
  let byte3 ← Silean.Modules.VectorLayout.place
    ReadFormatting.byte3Layout memRdata
  let halfValue ← mux highLane halfLow halfHigh
  let lowByteValue ← mux lowLane byte0 byte1
  let highByteValue ← mux lowLane byte2 byte3
  let byteValue ← mux highLane lowByteValue highByteValue
  let halfWordsize ← Silean.Modules.EqualsConstant.place
    memWordsize (stateOfNat 1)
  let byteWordsize ← Silean.Modules.EqualsConstant.place
    memWordsize (stateOfNat 2)
  let selectHalf ← mux halfWordsize memRdata halfValue
  output "mem_rdata_word" (← mux byteWordsize selectHalf byteValue)

noncomputable def description : Description := build construction

end ReadFormatting.Description

namespace ReadFormatting

noncomputable def placeNamed (name : Naming.SourceName)
    (memWordsize : Net (.vector 2 .bit))
    (regOp1 memRdata : Net (.vector 32 .bit)) :
    Builder (Net (.vector 32 .bit)) := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .mem_wordsize => memWordsize
    | .reg_op1 => regOp1
    | .mem_rdata => memRdata
  pure (child .mem_rdata_word)

noncomputable def place (memWordsize : Net (.vector 2 .bit))
    (regOp1 memRdata : Net (.vector 32 .bit)) :
    Builder (Net (.vector 32 .bit)) := do
  let child ← placeIndexed "memory_read_formatting" design fun
    | .mem_wordsize => memWordsize
    | .reg_op1 => regOp1
    | .mem_rdata => memRdata
  pure (child .mem_rdata_word)

attribute [circuit_description] placeNamed place

end ReadFormatting

end PicoRV.Memory
