import PicoRV.MemoryContract
import PicoRV.Authoring.CircuitLogic
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Modules.BinaryToOneHot.BinaryToOneHotDerived
import Silean.Modules.EqualsConstant.EqualsConstantDerived
import Silean.Modules.VectorLayout.VectorLayoutDerived
import Silean.Modules.VectorSlice.VectorSliceDerived

namespace PicoRV.Memory

open Silean
open Silean.Authoring
open Silean.Authoring.CircuitDescription
open PicoRV.Authoring
open scoped Silean.Authoring

/-! # Memory look-ahead

This combinational interface announces the next memory request while the
memory state is idle. Instruction addresses select the aligned next PC;
data requests select the aligned operand address. Write data and strobes are
formatted from the requested word size, with encoding 3 falling through to
the word forms. The expanded typed hierarchy and verification remain under
`Internal/`. -/

namespace Lookahead

module_ports ports where
  input resetn : .bit,
  input mem_do_prefetch : .bit,
  input mem_do_rinst : .bit,
  input mem_do_rdata : .bit,
  input mem_do_wdata : .bit,
  input next_pc : .vector 32 .bit,
  input reg_op1 : .vector 32 .bit,
  input reg_op2 : .vector 32 .bit,
  input mem_wordsize : .vector 2 .bit,
  input current (schema := MemoryState.schema) : stateType,
  output mem_la_read : .bit,
  output mem_la_write : .bit,
  output mem_la_addr : .vector 32 .bit,
  output mem_la_wdata : .vector 32 .bit,
  output mem_la_wstrb : .vector 4 .bit

def readValue (resetn prefetch rinst rdata : Bool)
    (current : stateType.Denote) : Bool :=
  memLaReadFrom resetn prefetch rinst rdata (stateMap.unpack current)

def writeValue (resetn wdata : Bool) (current : stateType.Denote) : Bool :=
  memLaWriteFrom resetn wdata (stateMap.unpack current)

module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule memLaRead where
    reads := [resetn, mem_do_prefetch, mem_do_rinst, mem_do_rdata, current]
    writes := { mem_la_read := readValue resetn mem_do_prefetch
      mem_do_rinst mem_do_rdata current }
  output_rule memLaWrite where
    reads := [resetn, mem_do_wdata, current]
    writes := { mem_la_write := writeValue resetn mem_do_wdata current }
  output_rule memLaAddr where
    reads := [mem_do_prefetch, mem_do_rinst, next_pc, reg_op1]
    writes := { mem_la_addr := memLaAddrFrom mem_do_prefetch mem_do_rinst
      next_pc reg_op1 }
  output_rule memLaWdata where
    reads := [mem_wordsize, reg_op2]
    writes := { mem_la_wdata := formattedWriteDataFrom mem_wordsize reg_op2 }
  output_rule memLaWstrb where
    reads := [mem_wordsize, reg_op1]
    writes := { mem_la_wstrb := formattedWriteMaskFrom mem_wordsize reg_op1 }
  state_rule := Silean.Contracts.Cycle.CycleStateRule.empty _

def alignedLayout (index : Fin 32) :
    Silean.Modules.VectorLayout.BitSource 32 :=
  if index.val < 2 then .constant false else .input index

def halfDataLayout (index : Fin 32) :
    Silean.Modules.VectorLayout.BitSource 32 :=
  .input ⟨index.val % 16, by omega⟩

def byteDataLayout (index : Fin 32) :
    Silean.Modules.VectorLayout.BitSource 32 :=
  .input ⟨index.val % 8, by omega⟩

open ports

noncomputable def construction : ModuleBuilder ports Unit := do
  let resetn ← input .resetn
  let memDoPrefetch ← input .mem_do_prefetch
  let memDoRinst ← input .mem_do_rinst
  let memDoRdata ← input .mem_do_rdata
  let memDoWdata ← input .mem_do_wdata
  let nextPc ← input .next_pc
  let regOp1 ← input .reg_op1
  let regOp2 ← input .reg_op2
  let memWordsize ← input .mem_wordsize
  let current ← input .current
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

  output .mem_la_read read
  output .mem_la_write write
  output .mem_la_addr address
  output .mem_la_wdata writeData
  output .mem_la_wstrb writeMask

noncomputable def description : Description :=
  ModuleBuilder.build Naming.ports construction

/-- All five look-ahead outputs exposed by an allowed boundary step. -/
theorem outputs_of_allowed {step : cycleContract.Step}
    (allowed : cycleContract.Allows step) :
    step.outputs .mem_la_read = readValue
        (step.inputs .resetn) (step.inputs .mem_do_prefetch)
        (step.inputs .mem_do_rinst) (step.inputs .mem_do_rdata)
        (step.inputs .current) ∧
      step.outputs .mem_la_write = writeValue
        (step.inputs .resetn) (step.inputs .mem_do_wdata)
        (step.inputs .current) ∧
      step.outputs .mem_la_addr = memLaAddrFrom
        (step.inputs .mem_do_prefetch) (step.inputs .mem_do_rinst)
        (step.inputs .next_pc) (step.inputs .reg_op1) ∧
      step.outputs .mem_la_wdata = formattedWriteDataFrom
        (step.inputs .mem_wordsize) (step.inputs .reg_op2) ∧
      step.outputs .mem_la_wstrb = formattedWriteMaskFrom
        (step.inputs .mem_wordsize) (step.inputs .reg_op1) :=
  ⟨cycleContract.mem_la_read allowed, cycleContract.mem_la_write allowed,
    cycleContract.mem_la_addr allowed, cycleContract.mem_la_wdata allowed,
    cycleContract.mem_la_wstrb allowed⟩

end Lookahead

end PicoRV.Memory
