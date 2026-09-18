import Silean.Examples.Fixtures.PicoRVDatapath
import Silean.Examples.PicoRV.DatapathTheorems
import Silean.FIRRTL

namespace Silean.Examples.Checks.PicoRVDatapathStandaloneChecks

open Silean
open Silean.FIRRTL
open Silean.Examples.PicoRV.Datapath
open Silean.Examples.Fixtures.PicoRVDatapath

/-! ## Registered timing

The datapath outputs expose the current register state, while the second
component returned by `cycleContract.evaluate` is the state captured at the
next edge. Reset therefore clears the next PC state without retroactively
changing the PC visible during the reset cycle. -/

def resetSource := stateWith 0x1000 0x2000 3 4 5 6 7

def resetCycle := cycleContract.evaluate
  (inputValues { idleInputs with resetn := false }) resetSource

example : BitVector.toNat 32 (resetCycle.1 .reg_pc) = 0x1000 := by decide
example : BitVector.toNat 32 (resetCycle.1 .reg_op1) = 3 := by decide
example : BitVector.toNat 32 (resetCycle.2 .reg_pc) = 0 := by decide
example : BitVector.toNat 32 (resetCycle.2 .reg_next_pc) = 0 := by decide

/-! ## Structural boundary

These witnesses ensure the executable examples above describe the same cycle
contract implemented by the concrete hierarchy, and that no behavioral
blackbox is hidden anywhere below this datapath. The render checks protect the
standalone hardware boundary used by generated-hardware tests. -/

noncomputable example : Contracts.Cycle.ModuleCycleCertified ports := certified

example : moduleStructure.HasNoBlackboxes := moduleStructure_hasNoBlackboxes

noncomputable example : RenderResult String := renderClosedCircuit naming

#guard match renderClosedCircuit naming with
  | .ok _ => true
  | .error _ => false

#guard renderModuleKey naming.key = "picorv32_datapath"

private def contains (text fragment : String) : Bool :=
  (text.splitOn fragment).length > 1

#guard match renderRootModule naming with
  | .error _ => false
  | .ok text =>
      ["public module picorv32_datapath",
       "inst storage",
       "inst alu",
       "inst next",
       "inst writeback",
       "output reg_pc : UInt<1>[32]",
       "output cpuregs_wrdata : UInt<1>[32]"].all (contains text)

end Silean.Examples.Checks.PicoRVDatapathStandaloneChecks
