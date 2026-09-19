import PicoRV.Memory.Internal.MemoryLookaheadStructure
import PicoRV.Authoring.CircuitLogic
import Silean.Modules.BinaryToOneHot.BinaryToOneHot
import Silean.Modules.EqualsConstant.EqualsConstant
import Silean.Modules.VectorLayout.VectorLayout
import Silean.Modules.VectorSlice.VectorSlice

namespace PicoRV.Memory

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring.CircuitLogic
open scoped Silean.Authoring.CircuitLogic

/-! # Memory look-ahead

This combinational interface announces the next memory request while the
memory state is idle. Instruction addresses select the aligned next PC;
data requests select the aligned operand address. Write data and strobes are
formatted from the requested word size, with encoding 3 falling through to
the word forms. The expanded typed hierarchy and verification remain under
`Internal/`. -/

namespace Lookahead.Description

noncomputable def construction : Builder Unit := do
  let resetn ← input "resetn" .bit
  let memDoPrefetch ← input "mem_do_prefetch" .bit
  let memDoRinst ← input "mem_do_rinst" .bit
  let memDoRdata ← input "mem_do_rdata" .bit
  let memDoWdata ← input "mem_do_wdata" .bit
  let nextPc ← input "next_pc" (.vector 32 .bit)
  let regOp1 ← input "reg_op1" (.vector 32 .bit)
  let regOp2 ← input "reg_op2" (.vector 32 .bit)
  let memWordsize ← input "mem_wordsize" (.vector 2 .bit)
  let current ← input "current" stateType
  let currentFields ← split MemoryState.layout current

  let idle ← Silean.Modules.EqualsConstant.place
    (currentFields .mem_state) (stateOfNat 0)
  let enabledIdle ← resetn &&& idle
  let instructionCommand ← memDoPrefetch ||| memDoRinst
  let readCommand ← instructionCommand ||| memDoRdata
  let read ← enabledIdle &&& readCommand
  let write ← enabledIdle &&& memDoWdata

  let alignedNextPc ← Silean.Modules.VectorLayout.place
    Lookahead.alignedLayout nextPc
  let alignedRegOp1 ← Silean.Modules.VectorLayout.place
    Lookahead.alignedLayout regOp1
  let address ← mux instructionCommand alignedRegOp1 alignedNextPc

  let halfData ← Silean.Modules.VectorLayout.place
    Lookahead.halfDataLayout regOp2
  let byteData ← Silean.Modules.VectorLayout.place
    Lookahead.byteDataLayout regOp2
  let halfWordsize ← Silean.Modules.EqualsConstant.place
    memWordsize (stateOfNat 1)
  let byteWordsize ← Silean.Modules.EqualsConstant.place
    memWordsize (stateOfNat 2)
  let selectedHalfData ← mux halfWordsize regOp2 halfData
  let writeData ← mux byteWordsize selectedHalfData byteData

  let lowAddress ← Silean.Modules.VectorSlice.place .bit 0 2 30 regOp1
  let highHalfBit ← Silean.Modules.VectorSlice.place .bit 1 1 30 regOp1
  let highHalf ← Silean.Modules.EqualsConstant.place
    highHalfBit (fun _ => true)
  let lowHalfMask ← constant (.vector 4 .bit) (maskOfNat 0x3)
  let highHalfMask ← constant (.vector 4 .bit) (maskOfNat 0xc)
  let halfMask ← mux highHalf lowHalfMask highHalfMask
  let byteMask ← Silean.Modules.BinaryToOneHot.place 2 lowAddress
  let wordMask ← constant (.vector 4 .bit) (maskOfNat 0xf)
  let selectedHalfMask ← mux halfWordsize wordMask halfMask
  let writeMask ← mux byteWordsize selectedHalfMask byteMask

  output "mem_la_read" read
  output "mem_la_write" write
  output "mem_la_addr" address
  output "mem_la_wdata" writeData
  output "mem_la_wstrb" writeMask

noncomputable def description : Description := build construction

end Lookahead.Description

namespace Lookahead

structure PlacedOutputs where
  memLaRead : Net .bit
  memLaWrite : Net .bit
  memLaAddr : Net (.vector 32 .bit)
  memLaWdata : Net (.vector 32 .bit)
  memLaWstrb : Net (.vector 4 .bit)

noncomputable def placeNamed (name : Naming.SourceName)
    (resetn memDoPrefetch memDoRinst memDoRdata memDoWdata : Net .bit)
    (nextPc regOp1 regOp2 : Net (.vector 32 .bit))
    (memWordsize : Net (.vector 2 .bit)) (current : Net stateType) :
    Builder PlacedOutputs := do
  let child ← Silean.Authoring.CircuitDescription.placeNamed name design fun
    | .resetn => resetn
    | .mem_do_prefetch => memDoPrefetch
    | .mem_do_rinst => memDoRinst
    | .mem_do_rdata => memDoRdata
    | .mem_do_wdata => memDoWdata
    | .next_pc => nextPc
    | .reg_op1 => regOp1
    | .reg_op2 => regOp2
    | .mem_wordsize => memWordsize
    | .current => current
  pure ⟨child .mem_la_read, child .mem_la_write, child .mem_la_addr,
    child .mem_la_wdata, child .mem_la_wstrb⟩

noncomputable def place
    (resetn memDoPrefetch memDoRinst memDoRdata memDoWdata : Net .bit)
    (nextPc regOp1 regOp2 : Net (.vector 32 .bit))
    (memWordsize : Net (.vector 2 .bit)) (current : Net stateType) :
    Builder PlacedOutputs := do
  let child ← placeIndexed "memory_lookahead" design fun
    | .resetn => resetn
    | .mem_do_prefetch => memDoPrefetch
    | .mem_do_rinst => memDoRinst
    | .mem_do_rdata => memDoRdata
    | .mem_do_wdata => memDoWdata
    | .next_pc => nextPc
    | .reg_op1 => regOp1
    | .reg_op2 => regOp2
    | .mem_wordsize => memWordsize
    | .current => current
  pure ⟨child .mem_la_read, child .mem_la_write, child .mem_la_addr,
    child .mem_la_wdata, child .mem_la_wstrb⟩

attribute [circuit_description] placeNamed place

end Lookahead

end PicoRV.Memory
