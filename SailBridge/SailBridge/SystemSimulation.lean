import RV32ISailBridge

/-!
Bridge for the two base RV32I SYSTEM instructions. Generated Sail reports a
`Trap` value at this executor boundary; it does not update privileged trap
CSRs or dispatch to a trap vector. The clean model deliberately identifies
only the unprivileged cause and preserves the faulting hart state.
-/

namespace RV32I.SailBridge

open LeanRV32D.Functions

/-- Minimal generated-state premise for these executors. Privilege is absent
from clean unprivileged state; the bridge retains it only to classify Sail's
more detailed trap result. -/
structure BaseSystemProfile (sail : SailState) where
  privilege : LeanRV32D.Privilege
  privilegeRead : LeanRV32D.readReg LeanRV32D.Register.cur_privilege sail =
    .ok privilege sail

/-- Exhaustive implemented ECALL profiles for the reviewed generation. This
form makes exclusion of the two unsupported virtual modes structural. -/
inductive BaseEcallProfile (sail : SailState) where
  | user (privilegeRead :
      LeanRV32D.readReg LeanRV32D.Register.cur_privilege sail = .ok .User sail)
  | supervisor (privilegeRead :
      LeanRV32D.readReg LeanRV32D.Register.cur_privilege sail =
        .ok .Supervisor sail)
  | machine (privilegeRead :
      LeanRV32D.readReg LeanRV32D.Register.cur_privilege sail = .ok .Machine sail)

/-- Relation between a clean unprivileged exception and Sail's executor-level
trap. ECALL deliberately forgets the privilege-specific environment-call
cause. EBREAK retains Sail's reviewed software-breakpoint construction without
importing its configurable `xtval` policy into the clean model. -/
inductive SystemTrapCorresponds (pc : RV32I.Address) :
    RV32I.Exception → LeanRV32D.ExecutionResult → Prop where
  | ecallUser : SystemTrapCorresponds pc .environmentCall
      (.Trap (.User,
        { trap := .E_U_EnvCall (), excinfo := none, ext := none }, pc))
  | ecallSupervisor : SystemTrapCorresponds pc .environmentCall
      (.Trap (.Supervisor,
        { trap := .E_S_EnvCall (), excinfo := none, ext := none }, pc))
  | ecallMachine : SystemTrapCorresponds pc .environmentCall
      (.Trap (.Machine,
        { trap := .E_M_EnvCall (), excinfo := none, ext := none }, pc))
  | ebreak (privilege : LeanRV32D.Privilege) :
      SystemTrapCorresponds pc .breakpoint
        (.Trap (privilege,
          make_sync_exception (.E_Breakpoint .Brk_Software) pc, pc))

theorem execute_ECALL_user {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail)
    (privilegeRead : LeanRV32D.readReg LeanRV32D.Register.cur_privilege sail =
      .ok .User sail) :
    execute_ECALL () sail = .ok (.Trap (.User,
      { trap := .E_U_EnvCall (), excinfo := none, ext := none }, state.pc)) sail := by
  have pcRead := readReg_of_get corresponds.pc
  simp [execute_ECALL, trap, privilegeRead, pcRead,
    bind, EStateM.bind, pure, EStateM.pure]

theorem execute_ECALL_supervisor {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail)
    (privilegeRead : LeanRV32D.readReg LeanRV32D.Register.cur_privilege sail =
      .ok .Supervisor sail) :
    execute_ECALL () sail = .ok (.Trap (.Supervisor,
      { trap := .E_S_EnvCall (), excinfo := none, ext := none }, state.pc)) sail := by
  have pcRead := readReg_of_get corresponds.pc
  simp [execute_ECALL, trap, privilegeRead, pcRead,
    bind, EStateM.bind, pure, EStateM.pure]

theorem execute_ECALL_machine {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail)
    (privilegeRead : LeanRV32D.readReg LeanRV32D.Register.cur_privilege sail =
      .ok .Machine sail) :
    execute_ECALL () sail = .ok (.Trap (.Machine,
      { trap := .E_M_EnvCall (), excinfo := none, ext := none }, state.pc)) sail := by
  have pcRead := readReg_of_get corresponds.pc
  simp [execute_ECALL, trap, privilegeRead, pcRead,
    bind, EStateM.bind, pure, EStateM.pure]

theorem execute_EBREAK_trap {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail)
    (profile : BaseSystemProfile sail) :
    execute_EBREAK () sail = .ok (.Trap (profile.privilege,
      make_sync_exception (.E_Breakpoint .Brk_Software) state.pc,
      state.pc)) sail := by
  have pcRead := readReg_of_get corresponds.pc
  simp [execute_EBREAK, trap, profile.privilegeRead, pcRead,
    bind, EStateM.bind, pure, EStateM.pure]

/-- Packaged comparison at the actual generated executor boundary. Both sides
retain their input state; this is exception production, not privileged trap
entry or a successful PC commitment. -/
structure DecodedSystemSimulation (state : RV32I.State) (sail : SailState)
    (instruction : RV32I.DecodedInstruction) (exception : RV32I.Exception)
    (executor : LeanRV32D.SailM LeanRV32D.ExecutionResult) where
  generated : LeanRV32D.ExecutionResult
  cleanExecution : RV32I.execute instruction state =
    .done (.raised state exception)
  actualExecutor : executor sail = .ok generated sail
  trapCorrespondence : SystemTrapCorresponds state.pc exception generated
  statePreserved : StateCorresponds state sail

def decoded_ecall_simulation {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail)
    (profile : BaseEcallProfile sail) :
    DecodedSystemSimulation state sail .ecall .environmentCall
      (execute_ECALL ()) := by
  cases profile with
  | user privilegeRead =>
      exact {
        generated := .Trap (.User,
          { trap := .E_U_EnvCall (), excinfo := none, ext := none }, state.pc)
        cleanExecution := by rfl
        actualExecutor := execute_ECALL_user corresponds privilegeRead
        trapCorrespondence := .ecallUser
        statePreserved := corresponds }
  | supervisor privilegeRead =>
      exact {
        generated := .Trap (.Supervisor,
          { trap := .E_S_EnvCall (), excinfo := none, ext := none }, state.pc)
        cleanExecution := by rfl
        actualExecutor := execute_ECALL_supervisor corresponds privilegeRead
        trapCorrespondence := .ecallSupervisor
        statePreserved := corresponds }
  | machine privilegeRead =>
      exact {
        generated := .Trap (.Machine,
          { trap := .E_M_EnvCall (), excinfo := none, ext := none }, state.pc)
        cleanExecution := by rfl
        actualExecutor := execute_ECALL_machine corresponds privilegeRead
        trapCorrespondence := .ecallMachine
        statePreserved := corresponds }

def decoded_ebreak_simulation {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail)
    (profile : BaseSystemProfile sail) :
    DecodedSystemSimulation state sail .ebreak .breakpoint
      (execute_EBREAK ()) :=
  { generated := .Trap (profile.privilege,
      make_sync_exception (.E_Breakpoint .Brk_Software) state.pc, state.pc)
    cleanExecution := by rfl
    actualExecutor := execute_EBREAK_trap corresponds profile
    trapCorrespondence := .ebreak profile.privilege
    statePreserved := corresponds }

end RV32I.SailBridge
