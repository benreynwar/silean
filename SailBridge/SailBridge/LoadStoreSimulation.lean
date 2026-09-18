import RV32ISailBridge

/-!
Decoded success and fault simulations for all five RV32I loads and all three
RV32I stores.  The generic generated-executor lemmas and path vocabulary live
in `RV32ISailBridge`; this module packages them with clean interaction traces.
-/

namespace RV32I.SailBridge

open LeanRV32D.Functions

/-- The earlier byte-backend LW proof is a concrete witness of the generic
successful path assumption for the ordinary Bare RAM profile. -/
def ordinaryLwSuccessPath {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (immediate : BitVec 12)
    (rs1 : RV32I.Register) (value : RV32I.Word)
    (path : GeneratedOrdinaryLwPath sail state immediate rs1)
    (present : SailWordAt sail (cleanLwAddress state immediate rs1) value) :
    GeneratedLoadSuccessPath sail state immediate rs1 .lw value where
  afterRead := sailSequentialStaged sail state
  route := by
    change LeanRV32D.Functions.vmem_read (sailRegister rs1)
      (sign_extend immediate) 4 (.Load .Data) false false false
      (sailSequentialStaged sail state) =
        sailOrdinaryLwRead rs1 (sign_extend immediate)
          (sailSequentialStaged sail state)
    exact path
  result := by
    change sailOrdinaryLwRead rs1 (sign_extend immediate)
      (sailSequentialStaged sail state) =
        .ok (.Ok value) (sailSequentialStaged sail state)
    exact sailOrdinaryLwRead_word corresponds immediate rs1 value present
  stateCorrespondence := by
    have staged := corresponds.stageNextPc
    exact { pc := staged.pc, register := staged.register }
  nextPc := by
    simp [sailSequentialStaged, sailSetReg]

/-- The earlier byte-update SW proof similarly discharges the generic store
path for the ordinary Bare RAM profile. -/
def ordinarySwSuccessPath {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (immediate : BitVec 12)
    (rs2 rs1 : RV32I.Register)
    (path : GeneratedOrdinarySwPath sail state immediate rs2 rs1) :
    GeneratedStoreSuccessPath sail state immediate rs2 rs1 .sw where
  afterWrite := sailSwWritten sail state immediate rs2 rs1
  route := by
    change LeanRV32D.Functions.vmem_write (sailRegister rs1)
      (sign_extend immediate) 4 (cleanSwValue state rs2) (.Store .Data)
      false false false (sailSequentialStaged sail state) =
        sailOrdinarySwWrite rs1 (sign_extend immediate)
          (cleanSwValue state rs2) (sailSequentialStaged sail state)
    exact path
  result := by
    change sailOrdinarySwWrite rs1 (sign_extend immediate)
      (cleanSwValue state rs2) (sailSequentialStaged sail state) =
        .ok (.Ok true) (sailSwWritten sail state immediate rs2 rs1)
    exact sailOrdinarySwWrite_word corresponds immediate rs2 rs1
  stateCorrespondence := by
    have stagedRelation := corresponds.stageNextPc
    have staged : StateCorresponds state (sailSequentialStaged sail state) :=
      { pc := stagedRelation.pc, register := stagedRelation.register }
    have written := staged.writeWordMemory (cleanSwAddress state immediate rs1)
      (cleanSwValue state rs2)
    simpa [sailSwWritten] using written
  nextPc := by
    change (sailSequentialStaged sail state).regs.get?
      LeanRV32D.Register.nextPC = some (RV32I.nextPc state)
    simp [sailSequentialStaged, sailSetReg]

theorem clean_execute_load (state : RV32I.State) (operation : BaseLoadOperation)
    (immediate : BitVec 12) (rs1 rd : RV32I.Register) :
    RV32I.execute (operation.instruction rd rs1 immediate) state =
      .request (.memory (.load (cleanDataAddress state immediate rs1)
        operation.width))
      (RV32I.finishLoad state rd (cleanDataAddress state immediate rs1)
        operation.width operation.unsigned) := by
  cases operation <;> rfl

theorem clean_execute_store (state : RV32I.State)
    (operation : BaseStoreOperation) (immediate : BitVec 12)
    (rs2 rs1 : RV32I.Register) :
    RV32I.execute (operation.instruction rs2 rs1 immediate) state =
      .request (.memory (.store (cleanDataAddress state immediate rs1)
        operation.width
        (RV32I.Instruction.storeValue operation.width (state.readRegister rs2))))
      (RV32I.finishStore state (cleanDataAddress state immediate rs1)
        operation.width
        (RV32I.Instruction.storeValue operation.width
          (state.readRegister rs2))) := by
  cases operation <;> rfl

theorem load_request_corresponds (state : RV32I.State)
    (operation : BaseLoadOperation) (immediate : BitVec 12)
    (rs1 : RV32I.Register) :
    DataRequestCorresponds
      (.load (cleanDataAddress state immediate rs1) operation.width)
      (.read operation.width
        (sailReadRequest (cleanDataAddress state immediate rs1)
          operation.width)) := by
  exact .load _ _

theorem store_request_corresponds (state : RV32I.State)
    (operation : BaseStoreOperation) (immediate : BitVec 12)
    (rs2 rs1 : RV32I.Register) :
    DataRequestCorresponds
      (.store (cleanDataAddress state immediate rs1) operation.width
        (RV32I.Instruction.storeValue operation.width (state.readRegister rs2)))
      (.write operation.width
        (sailWriteRequest (cleanDataAddress state immediate rs1) operation.width
          (RV32I.Instruction.storeValue operation.width
            (state.readRegister rs2)))) := by
  exact .store _ _ _

theorem clean_load_success_runs {environmentState : Type}
    (environment : RV32I.ExecutionEnvironment environmentState)
    {before after : environmentState} (state : RV32I.State)
    (operation : BaseLoadOperation) (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) (value : RV32I.AccessValue operation.width)
    (responds : environment.responds before
      (.memory (.load (cleanDataAddress state immediate rs1) operation.width))
      (.success value) after) :
    RV32I.Interaction.Runs environment
      (RV32I.execute (operation.instruction rd rs1 immediate) state) before
      [.memoryAccess
        { request := .load (cleanDataAddress state immediate rs1) operation.width
          response := .success value }]
      (.retired (cleanLoadPost state operation rd value)) after := by
  rw [clean_execute_load]
  apply RV32I.Interaction.Runs.request before after after
    (.memory (.load (cleanDataAddress state immediate rs1) operation.width))
    (.success value)
    (RV32I.finishLoad state rd (cleanDataAddress state immediate rs1)
      operation.width operation.unsigned)
    [] (.retired (cleanLoadPost state operation rd value)) responds
  simpa [cleanLoadPost] using
    (RV32I.Interaction.Runs.done after
      (RV32I.InstructionResult.retired (cleanLoadPost state operation rd value)))

theorem clean_store_success_runs {environmentState : Type}
    (environment : RV32I.ExecutionEnvironment environmentState)
    {before after : environmentState} (state : RV32I.State)
    (operation : BaseStoreOperation) (immediate : BitVec 12)
    (rs2 rs1 : RV32I.Register)
    (responds : environment.responds before
      (.memory (.store (cleanDataAddress state immediate rs1) operation.width
        (RV32I.Instruction.storeValue operation.width (state.readRegister rs2))))
      (.success ()) after) :
    RV32I.Interaction.Runs environment
      (RV32I.execute (operation.instruction rs2 rs1 immediate) state) before
      [.memoryAccess
        { request := .store (cleanDataAddress state immediate rs1) operation.width
            (RV32I.Instruction.storeValue operation.width
              (state.readRegister rs2))
          response := .success () }]
      (.retired (cleanStorePost state)) after := by
  rw [clean_execute_store]
  apply RV32I.Interaction.Runs.request before after after
    (.memory (.store (cleanDataAddress state immediate rs1) operation.width
      (RV32I.Instruction.storeValue operation.width (state.readRegister rs2))))
    (.success ())
    (RV32I.finishStore state (cleanDataAddress state immediate rs1)
      operation.width
      (RV32I.Instruction.storeValue operation.width (state.readRegister rs2)))
    [] (.retired (cleanStorePost state)) responds
  simpa [cleanStorePost] using
    (RV32I.Interaction.Runs.done after
      (RV32I.InstructionResult.retired (cleanStorePost state)))

noncomputable def sailDecodedLoadStep (operation : BaseLoadOperation)
    (immediate : BitVec 12) (rs1 rd : RV32I.Register) :
    LeanRV32D.SailM LeanRV32D.ExecutionResult := do
  stageSequentialPc
  let result ← LeanRV32D.Functions.execute_LOAD immediate
    (sailRegister rs1) (sailRegister rd) operation.unsigned
    operation.width.bytes
  LeanRV32D.Functions.tick_pc ()
  pure result

def sailLoadPost (state : RV32I.State) (operation : BaseLoadOperation)
    (rd : RV32I.Register) (value : RV32I.AccessValue operation.width)
    (afterRead : SailState) : SailState :=
  sailSetReg
    (sailWriteX afterRead rd
      (RV32I.Instruction.loadResult operation.width operation.unsigned value))
    LeanRV32D.Register.PC (RV32I.nextPc state)

theorem sailDecodedLoadStep_success {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (operation : BaseLoadOperation)
    (immediate : BitVec 12) (rs1 rd : RV32I.Register)
    (value : RV32I.AccessValue operation.width)
    (path : GeneratedLoadSuccessPath sail state immediate rs1 operation value) :
    sailDecodedLoadStep operation immediate rs1 rd sail =
      .ok (.Retire_Success ())
        (sailLoadPost state operation rd value path.afterRead) := by
  have stageEq : stageSequentialPc sail =
      .ok () (sailSequentialStaged sail state) := by
    rw [stageSequentialPc_of_corresponds corresponds]
    exact writeReg_eq_set sail (r := LeanRV32D.Register.nextPC)
      (RV32I.nextPc state)
  have executeEq := execute_LOAD_success immediate rs1 rd operation value path
  have nextPcFound :
      (sailWriteX path.afterRead rd
        (RV32I.Instruction.loadResult operation.width operation.unsigned value)).regs.get?
          LeanRV32D.Register.nextPC = some (RV32I.nextPc state) := by
    rw [sailWriteX_nextPc]
    exact path.nextPc
  have tickEq := tick_pc_of_nextPc nextPcFound
  simp only [sailDecodedLoadStep, bind, EStateM.bind, stageEq, executeEq,
    tickEq, pure, EStateM.pure]
  rfl

theorem sailLoadPost_corresponds {state : RV32I.State}
    (operation : BaseLoadOperation) (rd : RV32I.Register)
    (value : RV32I.AccessValue operation.width)
    {afterRead : SailState} (corresponds : StateCorresponds state afterRead) :
    StateCorresponds (cleanLoadPost state operation rd value)
      (sailLoadPost state operation rd value afterRead) := by
  have written := corresponds.writeX rd
    (RV32I.Instruction.loadResult operation.width operation.unsigned value)
  have committed := written.setPc (RV32I.nextPc state)
  simpa [cleanLoadPost, sailLoadPost] using committed

noncomputable def sailDecodedStoreStep (operation : BaseStoreOperation)
    (immediate : BitVec 12) (rs2 rs1 : RV32I.Register) :
    LeanRV32D.SailM LeanRV32D.ExecutionResult := do
  stageSequentialPc
  let result ← LeanRV32D.Functions.execute_STORE immediate
    (sailRegister rs2) (sailRegister rs1) operation.width.bytes
  LeanRV32D.Functions.tick_pc ()
  pure result

def sailStorePost (state : RV32I.State) (afterWrite : SailState) : SailState :=
  sailSetReg afterWrite LeanRV32D.Register.PC (RV32I.nextPc state)

theorem sailDecodedStoreStep_success {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (operation : BaseStoreOperation)
    (immediate : BitVec 12) (rs2 rs1 : RV32I.Register)
    (path : GeneratedStoreSuccessPath sail state immediate rs2 rs1 operation) :
    sailDecodedStoreStep operation immediate rs2 rs1 sail =
      .ok (.Retire_Success ()) (sailStorePost state path.afterWrite) := by
  have stageEq : stageSequentialPc sail =
      .ok () (sailSequentialStaged sail state) := by
    rw [stageSequentialPc_of_corresponds corresponds]
    exact writeReg_eq_set sail (r := LeanRV32D.Register.nextPC)
      (RV32I.nextPc state)
  have executeEq := execute_STORE_success corresponds immediate rs2 rs1
    operation path
  have tickEq := tick_pc_of_nextPc path.nextPc
  simp only [sailDecodedStoreStep, bind, EStateM.bind, stageEq, executeEq,
    tickEq, pure, EStateM.pure]
  rfl

theorem sailStorePost_corresponds (state : RV32I.State)
    {afterWrite : SailState} (corresponds : StateCorresponds state afterWrite) :
    StateCorresponds (cleanStorePost state) (sailStorePost state afterWrite) := by
  have committed := corresponds.setPc (RV32I.nextPc state)
  simpa [cleanStorePost, sailStorePost] using committed

inductive LoadFault (address : RV32I.Address) (width : RV32I.AccessWidth) where
  | accessFault
  | addressMisaligned (proof : ¬ width.Aligned address)

def LoadFault.response {address : RV32I.Address} {width : RV32I.AccessWidth}
    (fault : LoadFault address width) :
    RV32I.DataResponse width address (RV32I.AccessValue width) :=
  match fault with
  | .accessFault => .accessFault
  | .addressMisaligned proof => .addressMisaligned proof

def LoadFault.exception {address : RV32I.Address} {width : RV32I.AccessWidth}
    (fault : LoadFault address width) : RV32I.Exception :=
  match fault with
  | .accessFault => .loadAccessFault address
  | .addressMisaligned _ => .loadAddressMisaligned address

inductive StoreFault (address : RV32I.Address) (width : RV32I.AccessWidth) where
  | accessFault
  | addressMisaligned (proof : ¬ width.Aligned address)

def StoreFault.response {address : RV32I.Address} {width : RV32I.AccessWidth}
    (fault : StoreFault address width) : RV32I.DataResponse width address Unit :=
  match fault with
  | .accessFault => .accessFault
  | .addressMisaligned proof => .addressMisaligned proof

def StoreFault.exception {address : RV32I.Address} {width : RV32I.AccessWidth}
    (fault : StoreFault address width) : RV32I.Exception :=
  match fault with
  | .accessFault => .storeAccessFault address
  | .addressMisaligned _ => .storeAddressMisaligned address

/-- The generated executor failure must be the corresponding Sail trap, not
merely an arbitrary `ExecutionResult` returned by an assumed path equation.
Privilege and the generated trap-PC payload are intentionally existential:
they are outside the clean unprivileged architectural state. -/
inductive LoadExecutionFailureCorresponds {address : RV32I.Address}
    {width : RV32I.AccessWidth} :
    LoadFault address width → LeanRV32D.ExecutionResult → Prop where
  | accessFault (privilege : LeanRV32D.Privilege) (trapPc : RV32I.Word) :
      LoadExecutionFailureCorresponds (.accessFault)
        (.Trap (privilege,
          LeanRV32D.Functions.make_sync_exception
            (.E_Load_Access_Fault ()) address, trapPc))
  | addressMisaligned (proof : ¬ width.Aligned address)
      (privilege : LeanRV32D.Privilege) (trapPc : RV32I.Word) :
      LoadExecutionFailureCorresponds (.addressMisaligned proof)
        (.Trap (privilege,
          LeanRV32D.Functions.make_sync_exception
            (.E_Load_Addr_Align ()) address, trapPc))

inductive StoreExecutionFailureCorresponds {address : RV32I.Address}
    {width : RV32I.AccessWidth} :
    StoreFault address width → LeanRV32D.ExecutionResult → Prop where
  | accessFault (privilege : LeanRV32D.Privilege) (trapPc : RV32I.Word) :
      StoreExecutionFailureCorresponds (.accessFault)
        (.Trap (privilege,
          LeanRV32D.Functions.make_sync_exception
            (.E_SAMO_Access_Fault ()) address, trapPc))
  | addressMisaligned (proof : ¬ width.Aligned address)
      (privilege : LeanRV32D.Privilege) (trapPc : RV32I.Word) :
      StoreExecutionFailureCorresponds (.addressMisaligned proof)
        (.Trap (privilege,
          LeanRV32D.Functions.make_sync_exception
            (.E_SAMO_Addr_Align ()) address, trapPc))

theorem finishLoad_fault {address : RV32I.Address}
    {width : RV32I.AccessWidth}
    (state : RV32I.State) (rd : RV32I.Register) (unsigned : Bool)
    (fault : LoadFault address width) :
    RV32I.finishLoad state rd address width unsigned fault.response =
      .done (.raised state fault.exception) := by
  cases fault <;> rfl

theorem finishStore_fault {address : RV32I.Address}
    {width : RV32I.AccessWidth}
    (state : RV32I.State) (value : RV32I.AccessValue width)
    (fault : StoreFault address width) :
    RV32I.finishStore state address width value fault.response =
      .done (.raised state fault.exception) := by
  cases fault <;> rfl

structure GeneratedLoadFaultPath (sail : SailState) (state : RV32I.State)
    (immediate : BitVec 12) (rs1 : RV32I.Register)
    (operation : BaseLoadOperation)
    (fault : LoadFault (cleanDataAddress state immediate rs1) operation.width) where
  physicalResult : SailLoadResult operation.width
  physicalCorrespondence : LoadResponseCorresponds
    (address := cleanDataAddress state immediate rs1)
    (width := operation.width) fault.response physicalResult
  failure : LeanRV32D.ExecutionResult
  failureCorrespondence : LoadExecutionFailureCorresponds fault failure
  afterRead : SailState
  read : LeanRV32D.Functions.vmem_read (sailRegister rs1)
      (sign_extend immediate) operation.width.bytes (.Load .Data)
      false false false (sailSequentialStaged sail state) =
    .ok (.Err failure) afterRead
  stateCorrespondence : StateCorresponds state afterRead

theorem execute_LOAD_of_read_failure {sail : SailState} {state : RV32I.State}
    (immediate : BitVec 12) (rs1 rd : RV32I.Register)
    (width : RV32I.AccessWidth) (unsigned : Bool)
    (failure : LeanRV32D.ExecutionResult) (afterRead : SailState)
    (readResult : LeanRV32D.Functions.vmem_read (sailRegister rs1)
      (sign_extend immediate) width.bytes (.Load .Data) false false false
      (sailSequentialStaged sail state) = .ok (.Err failure) afterRead) :
    LeanRV32D.Functions.execute_LOAD immediate (sailRegister rs1)
        (sailRegister rd) unsigned width.bytes
        (sailSequentialStaged sail state) = .ok failure afterRead := by
  cases width <;> cases unsigned <;>
    simp [RV32I.AccessWidth.bytes] at readResult ⊢ <;>
    simp [LeanRV32D.Functions.execute_LOAD, readResult,
      LeanRV32D.assert, Sail.ConcurrencyInterfaceV1.PreSail.assert,
      LeanRV32D.Functions.xlen_bytes, bind, EStateM.bind, pure, EStateM.pure]

theorem execute_LOAD_failure {sail : SailState} {state : RV32I.State}
    (immediate : BitVec 12) (rs1 rd : RV32I.Register)
    (operation : BaseLoadOperation) {fault}
    (path : GeneratedLoadFaultPath sail state immediate rs1 operation fault) :
    LeanRV32D.Functions.execute_LOAD immediate (sailRegister rs1)
        (sailRegister rd) operation.unsigned operation.width.bytes
        (sailSequentialStaged sail state) = .ok path.failure path.afterRead :=
  execute_LOAD_of_read_failure immediate rs1 rd operation.width
    operation.unsigned path.failure path.afterRead path.read

structure GeneratedStoreFaultPath (sail : SailState) (state : RV32I.State)
    (immediate : BitVec 12) (rs2 rs1 : RV32I.Register)
    (operation : BaseStoreOperation)
    (fault : StoreFault (cleanDataAddress state immediate rs1) operation.width) where
  physicalResult : SailStoreResult
  physicalCorrespondence : StoreResponseCorresponds
    (address := cleanDataAddress state immediate rs1)
    (width := operation.width) fault.response physicalResult
  failure : LeanRV32D.ExecutionResult
  failureCorrespondence : StoreExecutionFailureCorresponds fault failure
  afterWrite : SailState
  write : LeanRV32D.Functions.vmem_write (sailRegister rs1)
      (sign_extend immediate) operation.width.bytes
      (toSailAccessValue operation.width
        (RV32I.Instruction.storeValue operation.width (state.readRegister rs2)))
      (.Store .Data) false false false (sailSequentialStaged sail state) =
    .ok (.Err failure) afterWrite
  stateCorrespondence : StateCorresponds state afterWrite

theorem execute_STORE_of_write_failure {sail : SailState} {state : RV32I.State}
    (corresponds : StateCorresponds state sail)
    (immediate : BitVec 12) (rs2 rs1 : RV32I.Register)
    (width : RV32I.AccessWidth) (failure : LeanRV32D.ExecutionResult)
    (afterWrite : SailState)
    (writeResult : LeanRV32D.Functions.vmem_write (sailRegister rs1)
      (sign_extend immediate) width.bytes
      (toSailAccessValue width
        (RV32I.Instruction.storeValue width (state.readRegister rs2)))
      (.Store .Data) false false false (sailSequentialStaged sail state) =
        .ok (.Err failure) afterWrite) :
    LeanRV32D.Functions.execute_STORE immediate (sailRegister rs2)
        (sailRegister rs1) width.bytes (sailSequentialStaged sail state) =
      .ok failure afterWrite := by
  have readSource := sw_staged_source_read corresponds rs2
  have extracted := extract_store_value width (state.readRegister rs2)
  cases width <;>
    simp [RV32I.AccessWidth.bytes] at extracted writeResult ⊢ <;>
    simp [LeanRV32D.Functions.execute_STORE, cleanSwValue,
      readSource, extracted, writeResult,
      LeanRV32D.assert, Sail.ConcurrencyInterfaceV1.PreSail.assert,
      LeanRV32D.Functions.xlen_bytes, bind, EStateM.bind, pure, EStateM.pure]

theorem execute_STORE_failure {sail : SailState} {state : RV32I.State}
    (corresponds : StateCorresponds state sail)
    (immediate : BitVec 12) (rs2 rs1 : RV32I.Register)
    (operation : BaseStoreOperation) {fault}
    (path : GeneratedStoreFaultPath sail state immediate rs2 rs1 operation fault) :
    LeanRV32D.Functions.execute_STORE immediate (sailRegister rs2)
        (sailRegister rs1) operation.width.bytes
        (sailSequentialStaged sail state) = .ok path.failure path.afterWrite :=
  execute_STORE_of_write_failure corresponds immediate rs2 rs1 operation.width
    path.failure path.afterWrite path.write

theorem clean_load_fault_runs {environmentState : Type}
    (environment : RV32I.ExecutionEnvironment environmentState)
    {before after : environmentState} (state : RV32I.State)
    (operation : BaseLoadOperation) (immediate : BitVec 12)
    (rs1 rd : RV32I.Register)
    (fault : LoadFault (cleanDataAddress state immediate rs1) operation.width)
    (responds : environment.responds before
      (.memory (.load (cleanDataAddress state immediate rs1) operation.width))
      fault.response after) :
    RV32I.Interaction.Runs environment
      (RV32I.execute (operation.instruction rd rs1 immediate) state) before
      [.memoryAccess
        { request := .load (cleanDataAddress state immediate rs1) operation.width
          response := fault.response }]
      (.raised state fault.exception) after := by
  rw [clean_execute_load]
  apply RV32I.Interaction.Runs.request before after after
    (.memory (.load (cleanDataAddress state immediate rs1) operation.width))
    fault.response
    (RV32I.finishLoad state rd (cleanDataAddress state immediate rs1)
      operation.width operation.unsigned)
    [] (.raised state fault.exception) responds
  rw [finishLoad_fault]
  exact RV32I.Interaction.Runs.done after
    (RV32I.InstructionResult.raised state fault.exception)

theorem clean_store_fault_runs {environmentState : Type}
    (environment : RV32I.ExecutionEnvironment environmentState)
    {before after : environmentState} (state : RV32I.State)
    (operation : BaseStoreOperation) (immediate : BitVec 12)
    (rs2 rs1 : RV32I.Register)
    (fault : StoreFault (cleanDataAddress state immediate rs1) operation.width)
    (responds : environment.responds before
      (.memory (.store (cleanDataAddress state immediate rs1) operation.width
        (RV32I.Instruction.storeValue operation.width (state.readRegister rs2))))
      fault.response after) :
    RV32I.Interaction.Runs environment
      (RV32I.execute (operation.instruction rs2 rs1 immediate) state) before
      [.memoryAccess
        { request := .store (cleanDataAddress state immediate rs1) operation.width
            (RV32I.Instruction.storeValue operation.width
              (state.readRegister rs2))
          response := fault.response }]
      (.raised state fault.exception) after := by
  rw [clean_execute_store]
  apply RV32I.Interaction.Runs.request before after after
    (.memory (.store (cleanDataAddress state immediate rs1) operation.width
      (RV32I.Instruction.storeValue operation.width (state.readRegister rs2))))
    fault.response
    (RV32I.finishStore state (cleanDataAddress state immediate rs1)
      operation.width
      (RV32I.Instruction.storeValue operation.width (state.readRegister rs2)))
    [] (.raised state fault.exception) responds
  rw [finishStore_fault]
  exact RV32I.Interaction.Runs.done after
    (RV32I.InstructionResult.raised state fault.exception)

theorem data_effective_address_eq_sail (state : RV32I.State)
    (immediate : BitVec 12) (rs1 : RV32I.Register) :
    cleanDataAddress state immediate rs1 =
      state.readRegister rs1 + sign_extend immediate := by
  simp [cleanDataAddress, RV32I.Instruction.address, sign_extend,
    Sail.BitVec.signExtend]

structure DecodedLoadSuccessSimulation {environmentState : Type}
    (environment : RV32I.ExecutionEnvironment environmentState)
    (before after : environmentState) (state : RV32I.State) (sail : SailState)
    (operation : BaseLoadOperation) (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) (value : RV32I.AccessValue operation.width) where
  effectiveAddress : cleanDataAddress state immediate rs1 =
    state.readRegister rs1 + sign_extend immediate
  requestCorrespondence : DataRequestCorresponds
    (.load (cleanDataAddress state immediate rs1) operation.width)
    (.read operation.width
      (sailReadRequest (cleanDataAddress state immediate rs1) operation.width))
  cleanRun : RV32I.Interaction.Runs environment
    (RV32I.execute (operation.instruction rd rs1 immediate) state) before
    [.memoryAccess
      { request := .load (cleanDataAddress state immediate rs1) operation.width
        response := .success value }]
    (.retired (cleanLoadPost state operation rd value)) after
  generatedPath : GeneratedLoadSuccessPath sail state immediate rs1 operation value
  sailExecution : sailDecodedLoadStep operation immediate rs1 rd sail =
    .ok (.Retire_Success ())
      (sailLoadPost state operation rd value generatedPath.afterRead)
  postCorrespondence : StateCorresponds (cleanLoadPost state operation rd value)
    (sailLoadPost state operation rd value generatedPath.afterRead)

def decoded_load_success_simulation {environmentState : Type}
    (environment : RV32I.ExecutionEnvironment environmentState)
    {before after : environmentState} {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (operation : BaseLoadOperation)
    (immediate : BitVec 12) (rs1 rd : RV32I.Register)
    (value : RV32I.AccessValue operation.width)
    (path : GeneratedLoadSuccessPath sail state immediate rs1 operation value)
    (responds : environment.responds before
      (.memory (.load (cleanDataAddress state immediate rs1) operation.width))
      (.success value) after) :
    DecodedLoadSuccessSimulation environment before after state sail operation
      immediate rs1 rd value where
  effectiveAddress := data_effective_address_eq_sail state immediate rs1
  requestCorrespondence := load_request_corresponds state operation immediate rs1
  cleanRun := clean_load_success_runs environment state operation immediate
    rs1 rd value responds
  generatedPath := path
  sailExecution := sailDecodedLoadStep_success corresponds operation immediate
    rs1 rd value path
  postCorrespondence := sailLoadPost_corresponds operation rd value
    path.stateCorrespondence

structure DecodedStoreSuccessSimulation {environmentState : Type}
    (environment : RV32I.ExecutionEnvironment environmentState)
    (before after : environmentState) (state : RV32I.State) (sail : SailState)
    (operation : BaseStoreOperation) (immediate : BitVec 12)
    (rs2 rs1 : RV32I.Register) where
  effectiveAddress : cleanDataAddress state immediate rs1 =
    state.readRegister rs1 + sign_extend immediate
  requestCorrespondence : DataRequestCorresponds
    (.store (cleanDataAddress state immediate rs1) operation.width
      (RV32I.Instruction.storeValue operation.width (state.readRegister rs2)))
    (.write operation.width
      (sailWriteRequest (cleanDataAddress state immediate rs1) operation.width
        (RV32I.Instruction.storeValue operation.width (state.readRegister rs2))))
  cleanRun : RV32I.Interaction.Runs environment
    (RV32I.execute (operation.instruction rs2 rs1 immediate) state) before
    [.memoryAccess
      { request := .store (cleanDataAddress state immediate rs1) operation.width
          (RV32I.Instruction.storeValue operation.width (state.readRegister rs2))
        response := .success () }]
    (.retired (cleanStorePost state)) after
  generatedPath : GeneratedStoreSuccessPath sail state immediate rs2 rs1 operation
  sailExecution : sailDecodedStoreStep operation immediate rs2 rs1 sail =
    .ok (.Retire_Success ()) (sailStorePost state generatedPath.afterWrite)
  postCorrespondence : StateCorresponds (cleanStorePost state)
    (sailStorePost state generatedPath.afterWrite)

def decoded_store_success_simulation {environmentState : Type}
    (environment : RV32I.ExecutionEnvironment environmentState)
    {before after : environmentState} {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (operation : BaseStoreOperation)
    (immediate : BitVec 12) (rs2 rs1 : RV32I.Register)
    (path : GeneratedStoreSuccessPath sail state immediate rs2 rs1 operation)
    (responds : environment.responds before
      (.memory (.store (cleanDataAddress state immediate rs1) operation.width
        (RV32I.Instruction.storeValue operation.width (state.readRegister rs2))))
      (.success ()) after) :
    DecodedStoreSuccessSimulation environment before after state sail operation
      immediate rs2 rs1 where
  effectiveAddress := data_effective_address_eq_sail state immediate rs1
  requestCorrespondence := store_request_corresponds state operation immediate rs2 rs1
  cleanRun := clean_store_success_runs environment state operation immediate
    rs2 rs1 responds
  generatedPath := path
  sailExecution := sailDecodedStoreStep_success corresponds operation immediate
    rs2 rs1 path
  postCorrespondence := sailStorePost_corresponds state path.stateCorrespondence

/-- Fault certificates stop at the generated instruction executor.  Unlike a
retired instruction, a fault does not perform the success-only `tick_pc`
commitment in this bridge statement. -/
structure DecodedLoadFaultSimulation {environmentState : Type}
    (environment : RV32I.ExecutionEnvironment environmentState)
    (before after : environmentState) (state : RV32I.State) (sail : SailState)
    (operation : BaseLoadOperation) (immediate : BitVec 12)
    (rs1 rd : RV32I.Register)
    (fault : LoadFault (cleanDataAddress state immediate rs1) operation.width) where
  effectiveAddress : cleanDataAddress state immediate rs1 =
    state.readRegister rs1 + sign_extend immediate
  requestCorrespondence : DataRequestCorresponds
    (.load (cleanDataAddress state immediate rs1) operation.width)
    (.read operation.width
      (sailReadRequest (cleanDataAddress state immediate rs1) operation.width))
  cleanRun : RV32I.Interaction.Runs environment
    (RV32I.execute (operation.instruction rd rs1 immediate) state) before
    [.memoryAccess
      { request := .load (cleanDataAddress state immediate rs1) operation.width
        response := fault.response }]
    (.raised state fault.exception) after
  generatedPath : GeneratedLoadFaultPath sail state immediate rs1 operation fault
  physicalCorrespondence : LoadResponseCorresponds
    (address := cleanDataAddress state immediate rs1) (width := operation.width)
    fault.response generatedPath.physicalResult
  failureCorrespondence : LoadExecutionFailureCorresponds fault
    generatedPath.failure
  sailExecution : LeanRV32D.Functions.execute_LOAD immediate (sailRegister rs1)
    (sailRegister rd) operation.unsigned operation.width.bytes
    (sailSequentialStaged sail state) =
      .ok generatedPath.failure generatedPath.afterRead
  preservedState : StateCorresponds state generatedPath.afterRead

def decoded_load_fault_simulation {environmentState : Type}
    (environment : RV32I.ExecutionEnvironment environmentState)
    {before after : environmentState} {state : RV32I.State} {sail : SailState}
    (operation : BaseLoadOperation) (immediate : BitVec 12)
    (rs1 rd : RV32I.Register)
    (fault : LoadFault (cleanDataAddress state immediate rs1) operation.width)
    (path : GeneratedLoadFaultPath sail state immediate rs1 operation fault)
    (responds : environment.responds before
      (.memory (.load (cleanDataAddress state immediate rs1) operation.width))
      fault.response after) :
    DecodedLoadFaultSimulation environment before after state sail operation
      immediate rs1 rd fault where
  effectiveAddress := data_effective_address_eq_sail state immediate rs1
  requestCorrespondence := load_request_corresponds state operation immediate rs1
  cleanRun := clean_load_fault_runs environment state operation immediate rs1 rd
    fault responds
  generatedPath := path
  physicalCorrespondence := path.physicalCorrespondence
  failureCorrespondence := path.failureCorrespondence
  sailExecution := execute_LOAD_failure immediate rs1 rd operation path
  preservedState := path.stateCorrespondence

structure DecodedStoreFaultSimulation {environmentState : Type}
    (environment : RV32I.ExecutionEnvironment environmentState)
    (before after : environmentState) (state : RV32I.State) (sail : SailState)
    (operation : BaseStoreOperation) (immediate : BitVec 12)
    (rs2 rs1 : RV32I.Register)
    (fault : StoreFault (cleanDataAddress state immediate rs1) operation.width) where
  effectiveAddress : cleanDataAddress state immediate rs1 =
    state.readRegister rs1 + sign_extend immediate
  requestCorrespondence : DataRequestCorresponds
    (.store (cleanDataAddress state immediate rs1) operation.width
      (RV32I.Instruction.storeValue operation.width (state.readRegister rs2)))
    (.write operation.width
      (sailWriteRequest (cleanDataAddress state immediate rs1) operation.width
        (RV32I.Instruction.storeValue operation.width (state.readRegister rs2))))
  cleanRun : RV32I.Interaction.Runs environment
    (RV32I.execute (operation.instruction rs2 rs1 immediate) state) before
    [.memoryAccess
      { request := .store (cleanDataAddress state immediate rs1) operation.width
          (RV32I.Instruction.storeValue operation.width (state.readRegister rs2))
        response := fault.response }]
    (.raised state fault.exception) after
  generatedPath : GeneratedStoreFaultPath sail state immediate rs2 rs1 operation fault
  physicalCorrespondence : StoreResponseCorresponds
    (address := cleanDataAddress state immediate rs1) (width := operation.width)
    fault.response generatedPath.physicalResult
  failureCorrespondence : StoreExecutionFailureCorresponds fault
    generatedPath.failure
  sailExecution : LeanRV32D.Functions.execute_STORE immediate (sailRegister rs2)
    (sailRegister rs1) operation.width.bytes (sailSequentialStaged sail state) =
      .ok generatedPath.failure generatedPath.afterWrite
  preservedState : StateCorresponds state generatedPath.afterWrite

def decoded_store_fault_simulation {environmentState : Type}
    (environment : RV32I.ExecutionEnvironment environmentState)
    {before after : environmentState} {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (operation : BaseStoreOperation)
    (immediate : BitVec 12) (rs2 rs1 : RV32I.Register)
    (fault : StoreFault (cleanDataAddress state immediate rs1) operation.width)
    (path : GeneratedStoreFaultPath sail state immediate rs2 rs1 operation fault)
    (responds : environment.responds before
      (.memory (.store (cleanDataAddress state immediate rs1) operation.width
        (RV32I.Instruction.storeValue operation.width (state.readRegister rs2))))
      fault.response after) :
    DecodedStoreFaultSimulation environment before after state sail operation
      immediate rs2 rs1 fault where
  effectiveAddress := data_effective_address_eq_sail state immediate rs1
  requestCorrespondence := store_request_corresponds state operation immediate rs2 rs1
  cleanRun := clean_store_fault_runs environment state operation immediate rs2 rs1
    fault responds
  generatedPath := path
  physicalCorrespondence := path.physicalCorrespondence
  failureCorrespondence := path.failureCorrespondence
  sailExecution := execute_STORE_failure corresponds immediate rs2 rs1 operation path
  preservedState := path.stateCorrespondence

end RV32I.SailBridge
