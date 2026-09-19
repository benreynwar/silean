import Silean.FIRRTL
import PicoRV.RegsTheorems

namespace PicoRVTests.Regs

open Silean Silean.FIRRTL

noncomputable example : Silean.Contracts.Cycle.ModuleCycleCertified
    PicoRV.Regs.ports :=
  PicoRV.Regs.certified

private def address (value : Fin 32) : PicoRV.Regs.RegisterAddress :=
  fun index => value.val / (2 ^ index.val) % 2 = 1

private def word (value : Bool) : PicoRV.Regs.Word := fun _ => value

private def inputs (resetn write : Bool) (rs1 rs2 rd : Fin 32) :
    PicoRV.Regs.ports.inputs.Values
  | .resetn => resetn
  | .decoded_rs1 => address rs1
  | .decoded_rs2 => address rs2
  | .cpuregs_write => write
  | .latched_rd => address rd
  | .cpuregs_wrdata => word true

private def initialState : PicoRV.Regs.stateMap.Values
  | .cpuregs => fun index => word (index = 3)

private def ordinaryWrite := PicoRV.Regs.cycleContract.evaluate
  (inputs true true 0 3 4) initialState

-- x0 reads as zero, while the other read port sees the current bank value.
#guard !(ordinaryWrite.1 .cpuregs_rs1 0)
#guard ordinaryWrite.1 .cpuregs_rs2 0
-- An enabled nonzero write appears in the next contract state.
#guard ordinaryWrite.2 .cpuregs 4 0

private def zeroWrite := PicoRV.Regs.cycleContract.evaluate
  (inputs true true 0 0 0) initialState

private def resetWrite := PicoRV.Regs.cycleContract.evaluate
  (inputs false true 0 0 4) initialState

-- Writes to x0 and writes while resetn is low leave all entries unchanged.
#guard !(zeroWrite.2 .cpuregs 0 0)
#guard !(resetWrite.2 .cpuregs 4 0)

-- The closed renderer checks and accepts the public concrete hierarchy.
noncomputable example : RenderResult String :=
  renderClosedCircuit PicoRV.Regs.naming

#guard renderModuleKey PicoRV.Regs.naming.key =
  "picorv32_regs"
#guard PicoRV.Regs.Naming.ports.inputs.name .resetn = "resetn"
#guard PicoRV.Regs.Naming.ports.inputs.name .decoded_rs1 = "decoded_rs1"
#guard PicoRV.Regs.Naming.ports.inputs.name .cpuregs_wrdata = "cpuregs_wrdata"
#guard PicoRV.Regs.Naming.ports.outputs.name .cpuregs_rs1 = "cpuregs_rs1"
#guard PicoRV.Regs.Naming.ports.outputs.name .cpuregs_rs2 = "cpuregs_rs2"

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

-- Render the actual root module without normalizing the much larger repeated
-- transitive hierarchy into this `.olean`.
#guard match renderRootModule PicoRV.Regs.naming with
  | .error _ => false
  | .ok text =>
      ["public module picorv32_regs",
       "input resetn : UInt<1>",
       "input decoded_rs1 : UInt<1>[5]",
       "input decoded_rs2 : UInt<1>[5]",
       "input cpuregs_write : UInt<1>",
       "input latched_rd : UInt<1>[5]",
       "input cpuregs_wrdata : UInt<1>[32]",
       "output cpuregs_rs1 : UInt<1>[32]",
       "output cpuregs_rs2 : UInt<1>[32]",
       "inst register_bank_0",
       "inst mux_0",
       "inst mux_1"].all (contains text)

end PicoRVTests.Regs
