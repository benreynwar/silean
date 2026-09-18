import RV32ISailBridge

/-!
Bridge for base RV32I FENCE and FENCE.TSO.  The clean model retains all four
architectural I/O/read/write classes.  The generated sequential Sail backend
retains the decoded fields, but its executable `sail_barrier` primitive is a
state-preserving operation and its FENCE executor selects barriers only from
the effective R/W bits.  The statements below keep those two facts separate.
-/

namespace RV32I.SailBridge

open LeanRV32D.Functions
open Sail.ConcurrencyInterfaceV1

/-- Re-encode a clean fence set in the ISA's `IORW` field order. -/
def sailFenceBits (set : RV32I.FenceSet) : BitVec 4 :=
  BitVec.ofNat 4
    ((if set.input then 8 else 0) +
      (if set.output then 4 else 0) +
      (if set.read then 2 else 0) +
      (if set.write then 1 else 0))

def emptyFenceSet : RV32I.FenceSet :=
  { input := false, output := false, read := false, write := false }

def writeFenceSet : RV32I.FenceSet :=
  { input := false, output := false, read := false, write := true }

@[simp] theorem FenceSet.ofBits_sailFenceBits (set : RV32I.FenceSet) :
    RV32I.FenceSet.ofBits (sailFenceBits set) = set := by
  cases set with
  | mk input output read write =>
      cases input <;> cases output <;> cases read <;> cases write <;> decide

/-- Field-level correspondence to actual generated instruction constructors.
Normal correspondence deliberately quantifies over `fm`, `rs1`, and `rd`:
the base specification requires implementations to ignore those reserved
fields.  Exact FENCE.TSO has its distinct generated constructor. -/
inductive FenceInstructionCorresponds :
    RV32I.Fence → LeanRV32D.instruction → Prop where
  | normal (fm : BitVec 4) (predecessor successor : RV32I.FenceSet)
      (rs rd : LeanRV32D.regidx) :
      FenceInstructionCorresponds (.normal predecessor successor)
        (.FENCE (fm, sailFenceBits predecessor, sailFenceBits successor, rs, rd))
  | tso : FenceInstructionCorresponds .tso (.FENCE_TSO ())
  /-- When Zihintpause is enabled, Sail decodes the architecturally vacuous
  `FENCE W,0` code point to its dedicated PAUSE constructor. -/
  | pause : FenceInstructionCorresponds (.normal writeFenceSet emptyFenceSet)
      (.PAUSE ())

/-- The generated executor's nine nonvacuous R/W barrier choices. `none`
means that at least one effective R/W set is empty. -/
def generatedFenceBarrier (predecessor successor : BitVec 4) (fiom : Bool) :
    Option LeanRV32D.barrier_kind :=
  let predecessor := effective_fence_set predecessor fiom
  let successor := effective_fence_set successor fiom
  match (predecessor.extractLsb' 0 2, successor.extractLsb' 0 2) with
  | (0b11, 0b11) => some .Barrier_RISCV_rw_rw
  | (0b10, 0b11) => some .Barrier_RISCV_r_rw
  | (0b10, 0b10) => some .Barrier_RISCV_r_r
  | (0b11, 0b01) => some .Barrier_RISCV_rw_w
  | (0b01, 0b01) => some .Barrier_RISCV_w_w
  | (0b01, 0b11) => some .Barrier_RISCV_w_rw
  | (0b11, 0b10) => some .Barrier_RISCV_rw_r
  | (0b10, 0b01) => some .Barrier_RISCV_r_w
  | (0b01, 0b10) => some .Barrier_RISCV_w_r
  | (_, _) => none

/-- The generated R/W-only selection expressed directly on clean fields.
This is not the eventual RVWMO ordering relation; it merely names which
generated barrier constructor the current Sail executor chooses. -/
def cleanRwBarrier (predecessor successor : RV32I.FenceSet) :
    Option LeanRV32D.barrier_kind :=
  match (predecessor.read, predecessor.write,
      successor.read, successor.write) with
  | (true, true, true, true) => some .Barrier_RISCV_rw_rw
  | (true, false, true, true) => some .Barrier_RISCV_r_rw
  | (true, false, true, false) => some .Barrier_RISCV_r_r
  | (true, true, false, true) => some .Barrier_RISCV_rw_w
  | (false, true, false, true) => some .Barrier_RISCV_w_w
  | (false, true, true, true) => some .Barrier_RISCV_w_rw
  | (true, true, true, false) => some .Barrier_RISCV_rw_r
  | (true, false, false, true) => some .Barrier_RISCV_r_w
  | (false, true, true, false) => some .Barrier_RISCV_w_r
  | _ => none

/-- With FIOM inactive, all four clean bits round-trip to the generated
instruction fields, while the current generated executor's barrier choice is
exactly the R/W projection. In particular, I/O bits are not silently equated
with R/W bits. -/
theorem generatedFenceBarrier_sailFenceBits_false
    (predecessor successor : RV32I.FenceSet) :
    generatedFenceBarrier (sailFenceBits predecessor)
      (sailFenceBits successor) false =
        cleanRwBarrier predecessor successor := by
  cases predecessor with
  | mk pi po pr pw =>
    cases successor with
    | mk si so sr sw =>
      cases pi <;> cases po <;> cases pr <;> cases pw <;>
        cases si <;> cases so <;> cases sr <;> cases sw <;> rfl

/-- FIOM's generated strengthening is also explicit: input implies read and
output implies write, exactly as in Sail's `effective_fence_set`. -/
theorem effective_fence_set_sailFenceBits_true (set : RV32I.FenceSet) :
    effective_fence_set (sailFenceBits set) true =
      sailFenceBits
        { set with
          read := set.read || set.input
          write := set.write || set.output } := by
  cases set with
  | mk input output read write =>
    cases input <;> cases output <;> cases read <;> cases write <;> rfl

/-- Exhaust the generated executor's two-bit R/W projections without relying
on a generated four-way match simplifier. -/
theorem bitVecTwo_cases (value : BitVec 2) :
    value = 0 ∨ value = 1 ∨ value = 2 ∨ value = 3 := by
  have bound := value.isLt
  have cases : value.toNat = 0 ∨ value.toNat = 1 ∨
      value.toNat = 2 ∨ value.toNat = 3 := by omega
  rcases cases with h | h | h | h
  · left; exact BitVec.eq_of_toNat_eq h
  · right; left; exact BitVec.eq_of_toNat_eq h
  · right; right; left; exact BitVec.eq_of_toNat_eq h
  · right; right; right; exact BitVec.eq_of_toNat_eq h

/-- In the generated sequential backend a barrier records no state, so every
normal FENCE executor retires successfully without changing generated state.
The field-selection theorem above is the non-erased ordering evidence. -/
theorem execute_FENCE_success
    {sail : SailState} {fiom : Bool}
  (fm predecessor successor : BitVec 4) (rs rd : LeanRV32D.regidx)
    (fiomActive : is_fiom_active () sail = .ok fiom sail) :
    execute_FENCE fm predecessor successor rs rd sail =
      .ok (.Retire_Success ()) sail := by
  simp only [execute_FENCE, bind, EStateM.bind, fiomActive]
  let pred := effective_fence_set predecessor fiom
  let succ := effective_fence_set successor fiom
  rcases bitVecTwo_cases (Sail.BitVec.extractLsb pred 1 0) with
      hp | hp | hp | hp <;>
    rcases bitVecTwo_cases (Sail.BitVec.extractLsb succ 1 0) with
      hs | hs | hs | hs <;>
    simp [pred, succ, hp, hs,
      LeanRV32D.ConcurrencyInterfaceV1.sail_barrier,
      Sail.ConcurrencyInterfaceV1.PreSail.sail_barrier,
      RETIRE_SUCCESS, pure, EStateM.pure] <;> rfl

theorem execute_FENCE_TSO_success (sail : SailState) :
    execute_FENCE_TSO () sail = .ok (.Retire_Success ()) sail := by
  simp [execute_FENCE_TSO, bind, EStateM.bind,
    LeanRV32D.ConcurrencyInterfaceV1.sail_barrier,
    Sail.ConcurrencyInterfaceV1.PreSail.sail_barrier, RETIRE_SUCCESS,
    pure, EStateM.pure]

theorem execute_PAUSE_success (sail : SailState) :
    (pure (execute_PAUSE ()) : LeanRV32D.SailM LeanRV32D.ExecutionResult) sail =
      .ok (.Retire_Success ()) sail := by
  rfl

/-- Successful clean FENCE execution produces exactly one fence effect and
retires only after the EEI acknowledges that ordering request. -/
theorem clean_fence_runs {environmentState : Type}
    (environment : RV32I.ExecutionEnvironment environmentState)
    {before after : environmentState} (state : RV32I.State)
    (fence : RV32I.Fence)
    (responds : environment.responds before (.fence fence) () after) :
    RV32I.Interaction.Runs environment (RV32I.execute (.fence fence) state)
      before [.fence fence]
      (.retired { state with pc := RV32I.nextPc state }) after := by
  apply RV32I.Interaction.Runs.request before after after (.fence fence) ()
    (RV32I.finishFence state fence) []
    (.retired { state with pc := RV32I.nextPc state }) responds
  exact RV32I.Interaction.Runs.done after _

/-- Generated stage/execute/commit fragment for an ordinary FENCE. -/
def sailDecodedFenceStep (fm predecessor successor : BitVec 4)
    (rs rd : LeanRV32D.regidx) : LeanRV32D.SailM LeanRV32D.ExecutionResult := do
  stageSequentialPc
  let result ← execute_FENCE fm predecessor successor rs rd
  tick_pc ()
  pure result

/-- Generated stage/execute/commit fragment for exact FENCE.TSO. -/
def sailDecodedFenceTsoStep : LeanRV32D.SailM LeanRV32D.ExecutionResult := do
  stageSequentialPc
  let result ← execute_FENCE_TSO ()
  tick_pc ()
  pure result

/-- Alternative generated path when the optional Zihintpause decoder claims
the base `FENCE W,0` hint code point. -/
def sailDecodedPauseStep : LeanRV32D.SailM LeanRV32D.ExecutionResult := do
  stageSequentialPc
  let result := execute_PAUSE ()
  tick_pc ()
  pure result

def cleanFencePost (state : RV32I.State) : RV32I.State :=
  { state with pc := RV32I.nextPc state }

def sailFencePost (sail : SailState) (state : RV32I.State) : SailState :=
  sailSetReg
    (sailSetReg sail LeanRV32D.Register.nextPC (RV32I.nextPc state))
    LeanRV32D.Register.PC (RV32I.nextPc state)

theorem sailFencePost_corresponds {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) :
    StateCorresponds (cleanFencePost state) (sailFencePost sail state) := by
  have staged := corresponds.stageNextPc
  have stagedCorresponds : StateCorresponds state
      (sailSetReg sail LeanRV32D.Register.nextPC (RV32I.nextPc state)) :=
    { pc := staged.pc, register := staged.register }
  simpa [cleanFencePost, sailFencePost] using
    stagedCorresponds.setPc (RV32I.nextPc state)

theorem sailDecodedFenceStep_success {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) {fiom : Bool}
    (fm predecessor successor : BitVec 4) (rs rd : LeanRV32D.regidx)
    (fiomActive : is_fiom_active ()
      (sailSetReg sail LeanRV32D.Register.nextPC (RV32I.nextPc state)) =
        .ok fiom
          (sailSetReg sail LeanRV32D.Register.nextPC (RV32I.nextPc state))) :
    sailDecodedFenceStep fm predecessor successor rs rd sail =
      .ok (.Retire_Success ()) (sailFencePost sail state) := by
  let staged := sailSetReg sail LeanRV32D.Register.nextPC (RV32I.nextPc state)
  have stageEq : stageSequentialPc sail = .ok () staged := by
    rw [stageSequentialPc_of_corresponds corresponds]
    exact writeReg_eq_set sail (r := LeanRV32D.Register.nextPC)
      (RV32I.nextPc state)
  have executeEq : execute_FENCE fm predecessor successor rs rd staged =
      .ok (.Retire_Success ()) staged := by
    simpa [staged] using
      execute_FENCE_success fm predecessor successor rs rd fiomActive
  have nextPcFound : staged.regs.get? LeanRV32D.Register.nextPC =
      some (RV32I.nextPc state) := by
    simp [staged, sailSetReg]
  have tickEq := tick_pc_of_nextPc nextPcFound
  simp only [sailDecodedFenceStep, bind, EStateM.bind, stageEq, executeEq, tickEq]
  rfl

theorem sailDecodedFenceTsoStep_success {state : RV32I.State}
    {sail : SailState} (corresponds : StateCorresponds state sail) :
    sailDecodedFenceTsoStep sail =
      .ok (.Retire_Success ()) (sailFencePost sail state) := by
  let staged := sailSetReg sail LeanRV32D.Register.nextPC (RV32I.nextPc state)
  have stageEq : stageSequentialPc sail = .ok () staged := by
    rw [stageSequentialPc_of_corresponds corresponds]
    exact writeReg_eq_set sail (r := LeanRV32D.Register.nextPC)
      (RV32I.nextPc state)
  have executeEq : execute_FENCE_TSO () staged =
      .ok (.Retire_Success ()) staged := execute_FENCE_TSO_success staged
  have nextPcFound : staged.regs.get? LeanRV32D.Register.nextPC =
      some (RV32I.nextPc state) := by
    simp [staged, sailSetReg]
  have tickEq := tick_pc_of_nextPc nextPcFound
  simp only [sailDecodedFenceTsoStep, bind, EStateM.bind, stageEq, executeEq, tickEq]
  rfl

theorem sailDecodedPauseStep_success {state : RV32I.State}
    {sail : SailState} (corresponds : StateCorresponds state sail) :
    sailDecodedPauseStep sail =
      .ok (.Retire_Success ()) (sailFencePost sail state) := by
  let staged := sailSetReg sail LeanRV32D.Register.nextPC (RV32I.nextPc state)
  have stageEq : stageSequentialPc sail = .ok () staged := by
    rw [stageSequentialPc_of_corresponds corresponds]
    exact writeReg_eq_set sail (r := LeanRV32D.Register.nextPC)
      (RV32I.nextPc state)
  have nextPcFound : staged.regs.get? LeanRV32D.Register.nextPC =
      some (RV32I.nextPc state) := by
    simp [staged, sailSetReg]
  have tickEq := tick_pc_of_nextPc nextPcFound
  simp only [sailDecodedPauseStep, execute_PAUSE, RETIRE_SUCCESS, bind,
    EStateM.bind, stageEq, tickEq]
  rfl

structure DecodedFenceSimulation {environmentState : Type}
    (environment : RV32I.ExecutionEnvironment environmentState)
    (before after : environmentState) (state : RV32I.State) (sail : SailState)
    (fence : RV32I.Fence) where
  cleanRun : RV32I.Interaction.Runs environment
    (RV32I.execute (.fence fence) state) before [.fence fence]
    (.retired (cleanFencePost state)) after
  postCorrespondence : StateCorresponds (cleanFencePost state)
    (sailFencePost sail state)
  generatedInstruction : LeanRV32D.instruction
  instructionCorrespondence :
    FenceInstructionCorresponds fence generatedInstruction
  sailExecution :
    match generatedInstruction with
    | .FENCE (fm, predecessor, successor, rs, rd) =>
        ∃ fiom,
          is_fiom_active ()
              (sailSetReg sail LeanRV32D.Register.nextPC (RV32I.nextPc state)) =
            .ok fiom
              (sailSetReg sail LeanRV32D.Register.nextPC (RV32I.nextPc state)) ∧
          sailDecodedFenceStep fm predecessor successor rs rd sail =
            .ok (.Retire_Success ()) (sailFencePost sail state)
    | .FENCE_TSO () =>
        sailDecodedFenceTsoStep sail =
          .ok (.Retire_Success ()) (sailFencePost sail state)
    | .PAUSE () =>
        sailDecodedPauseStep sail =
          .ok (.Retire_Success ()) (sailFencePost sail state)
    | _ => False

def decoded_normal_fence_simulation {environmentState : Type}
    (environment : RV32I.ExecutionEnvironment environmentState)
    {before after : environmentState} {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail)
    (fm : BitVec 4) (predecessor successor : RV32I.FenceSet)
    (rs rd : LeanRV32D.regidx) (fiom : Bool)
    (responds : environment.responds before
      (.fence (.normal predecessor successor)) () after)
    (fiomActive : is_fiom_active ()
      (sailSetReg sail LeanRV32D.Register.nextPC (RV32I.nextPc state)) =
        .ok fiom
          (sailSetReg sail LeanRV32D.Register.nextPC (RV32I.nextPc state))) :
    DecodedFenceSimulation environment before after state sail
      (.normal predecessor successor) where
  cleanRun := clean_fence_runs environment state _ responds
  postCorrespondence := sailFencePost_corresponds corresponds
  generatedInstruction := .FENCE
    (fm, sailFenceBits predecessor, sailFenceBits successor, rs, rd)
  instructionCorrespondence := .normal fm predecessor successor rs rd
  sailExecution := ⟨fiom, fiomActive,
    sailDecodedFenceStep_success corresponds fm _ _ rs rd fiomActive⟩

def decoded_fence_tso_simulation {environmentState : Type}
    (environment : RV32I.ExecutionEnvironment environmentState)
    {before after : environmentState} {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail)
    (responds : environment.responds before (.fence .tso) () after) :
    DecodedFenceSimulation environment before after state sail .tso where
  cleanRun := clean_fence_runs environment state .tso responds
  postCorrespondence := sailFencePost_corresponds corresponds
  generatedInstruction := .FENCE_TSO ()
  instructionCorrespondence := .tso
  sailExecution := sailDecodedFenceTsoStep_success corresponds

def decoded_pause_fence_simulation {environmentState : Type}
    (environment : RV32I.ExecutionEnvironment environmentState)
    {before after : environmentState} {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail)
    (responds : environment.responds before
      (.fence (.normal writeFenceSet emptyFenceSet)) () after) :
    DecodedFenceSimulation environment before after state sail
      (.normal writeFenceSet emptyFenceSet) where
  cleanRun := clean_fence_runs environment state _ responds
  postCorrespondence := sailFencePost_corresponds corresponds
  generatedInstruction := .PAUSE ()
  instructionCorrespondence := .pause
  sailExecution := sailDecodedPauseStep_success corresponds

end RV32I.SailBridge
