import Silean.Examples.PicoRV.Memory.Internal.MemoryLookaheadVerification

/-! # Memory Lookahead theorems

Supported verification boundary for the authored module. Structural schedules and
witness construction remain under the Internal directory.
-/

namespace Silean.Examples.PicoRV.Memory.Lookahead

open Silean

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
        (step.inputs .mem_wordsize) (step.inputs .reg_op1) := by
  exact ⟨(memLaReadRule_holds_iff _ _ _).mp (allowed.1 .memLaRead),
    (memLaWriteRule_holds_iff _ _ _).mp (allowed.1 .memLaWrite),
    (memLaAddrRule_holds_iff _ _ _).mp (allowed.1 .memLaAddr),
    (memLaWdataRule_holds_iff _ _ _).mp (allowed.1 .memLaWdata),
    (memLaWstrbRule_holds_iff _ _ _).mp (allowed.1 .memLaWstrb)⟩

theorem implements_contract :
    Contracts.Cycle.Implements moduleStructure cycleContract
      certification.stateCorresponds :=
  certification.implements

theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨certified.hasStructuralResult, certified.structuralResultUnique⟩

theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end Silean.Examples.PicoRV.Memory.Lookahead
