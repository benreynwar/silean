import RV32I.Execution

namespace RV32I

private def zeroRegisters : Vector Word 31 := Vector.replicate 31 0

private def initialState : State :=
  { pc := 0x1000
    registers := zeroRegisters }

example : Instruction.lui 0x12345 = 0x12345000 := by
  rfl

example : Instruction.lui 0x80000 = 0x80000000 := by
  rfl

example : Instruction.auipc 0x12345 0x1000 = 0x12346000 := by
  rfl

example :
    execute (.lui 1 0x12345) initialState =
      .done (.retired
        { initialState.writeRegister 1 0x12345000 with pc := 0x1004 }) := by
  rfl

example :
    execute (.auipc 1 0x12345) initialState =
      .done (.retired
        { initialState.writeRegister 1 0x12346000 with pc := 0x1004 }) := by
  rfl

example :
    execute (.lui 0 0x12345) initialState =
      .done (.retired { initialState with pc := 0x1004 }) := by
  rfl

example :
    execute (.auipc 0 0x12345) initialState =
      .done (.retired { initialState with pc := 0x1004 }) := by
  rfl

example :
    execute (.addi 1 0 5) initialState =
      .done (.retired { initialState.writeRegister 1 5 with pc := 0x1004 }) := by
  rfl

example :
    execute (.addi 0 0 5) initialState =
      .done (.retired { initialState with pc := 0x1004 }) := by
  rfl

/-- LW issues a request. Its response continuation covers successful access,
access fault, and (only when justified) address misalignment. -/
example :
    execute (.lw 1 0 0) initialState =
      .request
        (.memory (.load (Instruction.address 0 (initialState.readRegister 0)) .word))
        (finishLoad initialState 1
          (Instruction.address 0 (initialState.readRegister 0)) .word false) := by
  rfl

example :
    finishLoad initialState 1 0 .word false (.success 0x12345678) =
      .done (.retired { initialState.writeRegister 1 0x12345678 with pc := 0x1004 }) := by
  rfl

example :
    finishLoad initialState 1 0 .word false .accessFault =
      .done (.raised initialState (.loadAccessFault 0)) := by
  rfl

/-- The payload type exposes exactly the transferred byte lanes. -/
example (value : AccessValue .byte) : BitVec 8 := value
example (value : AccessValue .half) : BitVec 16 := value
example (value : AccessValue .word) : BitVec 32 := value

/-- Loading to x0 still performs the access; only the register write is
discarded. -/
example :
    execute (.lw 0 0 0) initialState =
      .request (.memory (.load 0 .word))
        (finishLoad initialState 0 0 .word false) := by
  rfl

example :
    finishLoad initialState 0 0 .word false (.success 0x12345678) =
      .done (.retired { initialState with pc := 0x1004 }) := by
  rfl

private def storeState : State := initialState.writeRegister 2 0x89abcdef

example :
    execute (.sw 2 0 4) storeState =
      let address := Instruction.address 4 (storeState.readRegister 0)
      let value := storeState.readRegister 2
      .request (.memory (.store address .word value))
        (finishStore storeState address .word value) := by
  rfl

example :
    finishStore storeState 4 .word 0x89abcdef (.success ()) =
      .done (.retired { storeState with pc := 0x1004 }) := by
  rfl

example :
    finishStore storeState 4 .word 0x89abcdef .accessFault =
      .done (.raised storeState (.storeAccessFault 4)) := by
  rfl

/-- A misaligned request is still presented to the EEI; the EEI may complete
it, reject it as an access fault, or return an address-misaligned exception. -/
example :
    execute (.lw 1 0 2) initialState =
      .request
        (.memory (.load (Instruction.address 2 (initialState.readRegister 0)) .word))
        (finishLoad initialState 1
          (Instruction.address 2 (initialState.readRegister 0)) .word false) := by
  rfl

example :
    finishLoad initialState 1 2 .word false (.success 0x12345678) =
      .done (.retired { initialState.writeRegister 1 0x12345678 with pc := 0x1004 }) := by
  rfl

example :
    finishStore storeState 2 .word 0x89abcdef (.success ()) =
      .done (.retired { storeState with pc := 0x1004 }) := by
  rfl

example :
    finishLoad initialState 1 2 .word false .accessFault =
      .done (.raised initialState (.loadAccessFault 2)) := by
  rfl

example :
    finishStore storeState 2 .word 0x89abcdef .accessFault =
      .done (.raised storeState (.storeAccessFault 2)) := by
  rfl

example (misaligned : ¬ AccessWidth.word.Aligned 2) :
    finishLoad initialState 1 2 .word false (.addressMisaligned misaligned) =
      .done (.raised initialState (.loadAddressMisaligned 2)) := by
  rfl

example (misaligned : ¬ AccessWidth.word.Aligned 2) :
    finishStore storeState 2 .word 0x89abcdef (.addressMisaligned misaligned) =
      .done (.raised storeState (.storeAddressMisaligned 2)) := by
  rfl

example (response : DataResponse .word 4 Word) :
    ¬ response.IsAddressMisaligned :=
  DataResponse.not_addressMisaligned_of_aligned (by decide) response

private def fullFenceSet : FenceSet :=
  { input := true, output := true, read := true, write := true }

private def fullFence : Fence := .normal fullFenceSet fullFenceSet

/-- FENCE is a separately acknowledged ordering action, not a load/store. -/
example :
    execute (.fence fullFence) initialState =
      .request (.fence fullFence) (finishFence initialState fullFence) := by
  rfl

example :
    finishFence initialState fullFence () =
      .done (.retired { initialState with pc := 0x1004 }) := by
  rfl

example : Request.effect (.fence fullFence) () = .fence fullFence := by
  rfl

private theorem initialPcAligned : initialState.pc.toNat % 4 = 0 := by
  decide

/-! Focused decoder checks. The examples use ordinary RV32 encodings and test
U-, I-, and S-type immediate layouts, required funct3 values, and rejection. -/

example :
    Decoder.decode 0x123452b7 = some (.lui 5 0x12345) := by
  rfl

example :
    Decoder.decode 0xabcde317 = some (.auipc 6 0xabcde) := by
  rfl

example : Decoder.uImmediate 0xabcde317 = 0xabcde := by
  rfl

example :
    Decoder.decode 0x00500093 = some (.addi 1 0 5) := by
  rfl

example :
    Decoder.decode 0xfff10093 = some (.addi 1 2 0xfff) := by
  rfl

example :
    Decoder.decode 0xffc32283 = some (.lw 5 6 0xffc) := by
  rfl

example : Decoder.decode 0xffc30283 = some (.lb 5 6 0xffc) := by rfl
example : Decoder.decode 0xffc31283 = some (.lh 5 6 0xffc) := by rfl
example : Decoder.decode 0xffc34283 = some (.lbu 5 6 0xffc) := by rfl
example : Decoder.decode 0xffc35283 = some (.lhu 5 6 0xffc) := by rfl

example :
    Decoder.decode 0xfe742c23 = some (.sw 7 8 0xff8) := by
  rfl

example : Decoder.decode 0xfe740c23 = some (.sb 7 8 0xff8) := by rfl
example : Decoder.decode 0xfe741c23 = some (.sh 7 8 0xff8) := by rfl

/-- The encoded negative immediates have the expected XLEN-wide signed
interpretation used by instruction execution. -/
example : (Decoder.iImmediate 0xfff10093).signExtend 32 = 0xffffffff := by
  rfl

example : (Decoder.sImmediate 0xfe742c23).signExtend 32 = 0xfffffff8 := by
  rfl

/-! The remaining OP-IMM encodings, including all three legal RV32 shift
forms. Shift amounts are five-bit operands; bits 31:25 must have the exact
base-ISA values below. -/

example : Decoder.decode 0xfff12093 = some (.slti 1 2 0xfff) := by rfl
example : Decoder.decode 0xfff13093 = some (.sltiu 1 2 0xfff) := by rfl
example : Decoder.decode 0xfff14093 = some (.xori 1 2 0xfff) := by rfl
example : Decoder.decode 0xfff16093 = some (.ori 1 2 0xfff) := by rfl
example : Decoder.decode 0xfff17093 = some (.andi 1 2 0xfff) := by rfl
example : Decoder.decode 0x01f11093 = some (.slli 1 2 31) := by rfl
example : Decoder.decode 0x01f15093 = some (.srli 1 2 31) := by rfl
example : Decoder.decode 0x41f15093 = some (.srai 1 2 31) := by rfl

/-- Nonzero reserved shift-immediate upper bits are not silently accepted. -/
example : Decoder.decode 0x21f11093 = none := by rfl
example : Decoder.decode 0x21f15093 = none := by rfl

/-! Every base OP encoding, in assembly operand order `rd, rs1, rs2`. -/

example : Decoder.decode 0x003100b3 = some (.add 1 2 3) := by rfl
example : Decoder.decode 0x403100b3 = some (.sub 1 2 3) := by rfl
example : Decoder.decode 0x003110b3 = some (.sll 1 2 3) := by rfl
example : Decoder.decode 0x003120b3 = some (.slt 1 2 3) := by rfl
example : Decoder.decode 0x003130b3 = some (.sltu 1 2 3) := by rfl
example : Decoder.decode 0x003140b3 = some (.xor 1 2 3) := by rfl
example : Decoder.decode 0x003150b3 = some (.srl 1 2 3) := by rfl
example : Decoder.decode 0x403150b3 = some (.sra 1 2 3) := by rfl
example : Decoder.decode 0x003160b3 = some (.or 1 2 3) := by rfl
example : Decoder.decode 0x003170b3 = some (.and 1 2 3) := by rfl

/-- Other OP `funct7` values are reserved rather than aliases. -/
example : Decoder.decode 0x203100b3 = none := by rfl

/-! Control-transfer decoding reconstructs the scattered B- and J-immediates,
and accepts exactly the six RV32I branch conditions and the required JALR
funct3. -/

example : Decoder.decode 0x00208463 = some (.beq 1 2 8) := by rfl
example : Decoder.decode 0x00209463 = some (.bne 1 2 8) := by rfl
example : Decoder.decode 0x0020c463 = some (.blt 1 2 8) := by rfl
example : Decoder.decode 0x0020d463 = some (.bge 1 2 8) := by rfl
example : Decoder.decode 0x0020e463 = some (.bltu 1 2 8) := by rfl
example : Decoder.decode 0x0020f463 = some (.bgeu 1 2 8) := by rfl
example : Decoder.decode 0xfe208ce3 = some (.beq 1 2 0x1ff8) := by rfl
example : Decoder.decode 0x008000ef = some (.jal 1 8) := by rfl
example : Decoder.decode 0x004100e7 = some (.jalr 1 2 4) := by rfl
example : Decoder.decode 0x004110e7 = none := by rfl

example : Decoder.bImmediate 0xfe208ce3 = 0x1ff8 := by rfl
example : (Decoder.bImmediate 0xfe208ce3).signExtend 32 = 0xfffffff8 := by rfl
example : Decoder.jImmediate 0x008000ef = 8 := by rfl

/-! Arithmetic edge cases: immediate comparison uses sign extension even for
SLTIU, arithmetic shifts replicate the sign bit, and register shifts mask the
amount to its low five bits. -/

example : Instruction.slti 0xfff 0 = 0 := by native_decide
example : Instruction.sltiu 0xfff 0 = 1 := by native_decide
example : Instruction.xori 0xfff 0x12345678 = 0xedcba987 := by native_decide
example : Instruction.add 1 0xffffffff = 0 := by native_decide
example : Instruction.sub 1 0 = 0xffffffff := by native_decide
example : Instruction.srai 4 0x80000000 = 0xf8000000 := by native_decide
example : Instruction.sll 36 1 = 16 := by native_decide
example : Instruction.sra 36 0x80000000 = 0xf8000000 := by native_decide

example : Instruction.blt 0xffffffff 0 = false := by native_decide
example : Instruction.blt 0 0xffffffff = true := by native_decide
example : Instruction.bltu 0xffffffff 0 = true := by native_decide
example : Instruction.bltu 0 0xffffffff = false := by native_decide
example : Instruction.pcRelativeTarget (0x1ff8 : BitVec 13) 0x1000 = 0x0ff8 := by
  rfl
example : Instruction.pcRelativeTarget (8 : BitVec 21) 0xfffffffc = 4 := by
  rfl
example : Instruction.jalrTarget 0 0x1003 = 0x1002 := by native_decide

/-- Data effective-address addition wraps modulo `2^32`. -/
example : Instruction.address (1 : BitVec 12) 0xffffffff = 0 := by rfl
example : Instruction.address (0xfff : BitVec 12) 0 = 0xffffffff := by rfl

/-! Load extension and store-lane selection are explicit width-indexed value
operations, independent of the EEI response policy. -/

example : Instruction.loadResult .byte false 0x80 = 0xffffff80 := by rfl
example : Instruction.loadResult .byte true 0x80 = 0x00000080 := by rfl
example : Instruction.loadResult .half false 0x8001 = 0xffff8001 := by rfl
example : Instruction.loadResult .half true 0x8001 = 0x00008001 := by rfl
example : Instruction.loadResult .word false 0x89abcdef = 0x89abcdef := by rfl
example : Instruction.storeValue .byte 0x89abcdef = 0xef := by rfl
example : Instruction.storeValue .half 0x89abcdef = 0xcdef := by rfl
example : Instruction.storeValue .word 0x89abcdef = 0x89abcdef := by rfl

example :
    execute (.lb 1 0 0) initialState =
      .request (.memory (.load 0 .byte))
        (finishLoad initialState 1 0 .byte false) := by rfl

example :
    execute (.lhu 1 0 2) initialState =
      .request (.memory (.load 2 .half))
        (finishLoad initialState 1 2 .half true) := by rfl

example :
    finishLoad initialState 1 0 .byte false (.success 0x80) =
      .done (.retired
        { initialState.writeRegister 1 0xffffff80 with pc := 0x1004 }) := by
  rfl

example :
    finishLoad initialState 1 0 .half true (.success 0x8001) =
      .done (.retired
        { initialState.writeRegister 1 0x00008001 with pc := 0x1004 }) := by
  rfl

/-- A narrow load to x0 still completes the access and advances PC. -/
example :
    finishLoad initialState 0 0 .byte false (.success 0x80) =
      .done (.retired { initialState with pc := 0x1004 }) := by
  rfl

example :
    execute (.sb 2 0 0) storeState =
      .request (.memory (.store 0 .byte 0xef))
        (finishStore storeState 0 .byte 0xef) := by rfl

example :
    execute (.sh 2 0 2) storeState =
      .request (.memory (.store 2 .half 0xcdef))
        (finishStore storeState 2 .half 0xcdef) := by rfl

private def branchState : State :=
  (initialState.writeRegister 1 5).writeRegister 2 7

example :
    execute (.blt 1 2 8) branchState =
      .done (.retired { branchState with pc := 0x1008 }) := by
  rfl

example :
    execute (.bge 1 2 2) branchState =
      .done (.retired { branchState with pc := 0x1004 }) := by
  rfl

/-- An untaken branch never checks its unused target. -/
example :
    execute (.beq 1 2 2) branchState =
      .done (.retired { branchState with pc := 0x1004 }) := by
  rfl

example :
    execute (.jal 1 8) initialState =
      .done (.retired
        { initialState.writeRegister 1 0x1004 with pc := 0x1008 }) := by
  rfl

example :
    execute (.jal 0 8) initialState =
      .done (.retired { initialState with pc := 0x1008 }) := by
  rfl

private def jalrState : State := initialState.writeRegister 2 0x2003

example :
    execute (.jalr 1 2 0) jalrState =
      .done (.raised jalrState (.instructionAddressMisaligned 0x2002)) := by
  rfl

/-- The failed JALR leaves x1 untouched because the link write is conditional
on accepting the target. -/
example : jalrState.readRegister 1 = 0 := by rfl

example :
    execute (.jalr 1 2 2) jalrState =
      .done (.retired { jalrState.writeRegister 1 0x1004 with pc := 0x2004 }) := by
  rfl

example :
    execute (.jal 1 2) initialState =
      .done (.raised initialState (.instructionAddressMisaligned 0x1002)) := by
  rfl

example :
    execute (.sltiu 1 0 0xfff) initialState =
      .done (.retired { initialState.writeRegister 1 1 with pc := 0x1004 }) := by
  rfl

example :
    execute (.srai 0 0 4) initialState =
      .done (.retired { initialState with pc := 0x1004 }) := by
  rfl

/-- funct3=011 under LOAD would encode LD in RV64 but is not an RV32I load. -/
example : Decoder.decode 0x00003083 = none := by
  rfl

/-- Other reserved base load/store width encodings remain illegal. -/
example : Decoder.decode 0x00006083 = none := by rfl
example : Decoder.decode 0x00003023 = none := by rfl

example :
    Decoder.decodeAndExecute 0x00003083 initialState =
      .done (.raised initialState (.illegalInstruction 0x00003083)) := by
  rfl

/-- Normal FENCE preserves all four predecessor/successor bit classes. -/
example : Decoder.decode 0x0ff0000f = some (.fence fullFence) := by
  rfl

/-- Only the exact standard word receives the weaker TSO ordering. -/
example : Decoder.decode 0x8330000f = some (.fence .tso) := by
  rfl

/-- A reserved `fm=1000` configuration is treated as normal FENCE, and its
nonzero reserved register fields are ignored rather than made illegal. -/
example : Decoder.decode 0x8330818f =
    some (.fence (.normal
      { input := false, output := false, read := true, write := true }
      { input := false, output := false, read := true, write := true })) := by
  rfl

/-- Empty predecessor and successor sets are a vacuous but legal fence. -/
example : Decoder.decode 0x0000000f =
    some (.fence (.normal
      { input := false, output := false, read := false, write := false }
      { input := false, output := false, read := false, write := false })) := by
  rfl

/-- PAUSE's code point is the architecturally vacuous `FENCE W,0` hint in the
base interpretation. A bridge may also relate it to Sail's optional dedicated
PAUSE constructor. -/
example : Decoder.decode 0x0100000f =
    some (.fence (.normal
      { input := false, output := false, read := false, write := true }
      { input := false, output := false, read := false, write := false })) := by
  rfl

/-- FENCE.I is Zifencei, not base RV32I. -/
example : Decoder.decode 0x0000100f = none := by rfl

/-! Base SYSTEM contains exactly ECALL and EBREAK. Both raise a precise
unprivileged exception at the unchanged faulting state; trap entry belongs to
the surrounding execution environment or a separate privileged model. -/

example : Decoder.decode 0x00000073 = some .ecall := by rfl
example : Decoder.decode 0x00100073 = some .ebreak := by rfl

example : execute .ecall initialState =
    .done (.raised initialState .environmentCall) := by
  rfl

example : execute .ebreak initialState =
    .done (.raised initialState .breakpoint) := by
  rfl

/-- SYSTEM words that name privileged, CSR/counter, or extension operations
are not silently admitted into base RV32I. -/
example : Decoder.decode 0x30200073 = none := by rfl -- MRET
example : Decoder.decode 0x10500073 = none := by rfl -- WFI
example : Decoder.decode 0x12000073 = none := by rfl -- SFENCE.VMA
example : Decoder.decode 0x00001073 = none := by rfl -- CSRRW
example : Decoder.decode 0xc0002073 = none := by rfl -- RDCYCLE/CSRRS

example :
    Decoder.decodeAndExecute 0x30200073 initialState =
      .done (.raised initialState (.illegalInstruction 0x30200073)) := by
  rfl

example :
    Decoder.decodeAndExecute 0x8330000f initialState =
      .request (.fence .tso) (finishFence initialState .tso) := by
  rfl

example : Decoder.decode 0x00000000 = none := by
  rfl

/-- The concrete decoder is connected to the existing fetch boundary. -/
example :
    Decoder.fetchDecodeExecute initialState initialPcAligned =
      .request (.memory (.fetch initialState.pc initialPcAligned))
        (finishFetch initialState initialPcAligned Decoder.decodeAndExecute) := by
  rfl

example :
    finishFetch initialState initialPcAligned Decoder.decodeAndExecute
        (.success 0x00500093) =
      .done (.retired
        { initialState.writeRegister 1 5 with pc := 0x1004 }) := by
  rfl

example :
    finishFetch initialState initialPcAligned Decoder.decodeAndExecute
        (.success 0x123450b7) =
      .done (.retired
        { initialState.writeRegister 1 0x12345000 with pc := 0x1004 }) := by
  rfl

example :
    finishFetch initialState initialPcAligned Decoder.decodeAndExecute
        (.success 0x12345097) =
      .done (.retired
        { initialState.writeRegister 1 0x12346000 with pc := 0x1004 }) := by
  rfl

example :
    finishFetch initialState initialPcAligned Decoder.decodeAndExecute
        (.success 0xffc32283) =
      .request (.memory (.load 0xfffffffc .word))
        (finishLoad initialState 5 0xfffffffc .word false) := by
  rfl

example :
    finishFetch initialState initialPcAligned Decoder.decodeAndExecute
        (.success 0xfe742c23) =
      .request (.memory (.store 0xfffffff8 .word 0))
        (finishStore initialState 0xfffffff8 .word 0) := by
  rfl

example :
    finishFetch initialState initialPcAligned Decoder.decodeAndExecute
        (.success 0x00003083) =
      .done (.raised initialState (.illegalInstruction 0x00003083)) := by
  rfl

private def afterAddi8 : State :=
  { initialState.writeRegister 1 8 with pc := 0x1004 }

private theorem afterAddi8PcAligned : afterAddi8.pc.toNat % 4 = 0 := by
  decide

private def afterLw (value : Word) : State :=
  { afterAddi8.writeRegister 2 value with pc := 0x1008 }

private def afterSw : State :=
  { afterAddi8 with pc := 0x1008 }

/-- An abstract EEI response chain witnesses ADDI followed by LW. The trace
orders both fetches before the load and records retirement separately. -/
example {environmentState : Type}
    (environment : ExecutionEnvironment environmentState)
    (eei0 eei1 eei2 eei3 : environmentState)
    (value : Word)
    (fetchAddi :
      environment.responds eei0
        (.memory (.fetch initialState.pc initialPcAligned))
        (.success 0x00800093) eei1)
    (fetchLw :
      environment.responds eei1
        (.memory (.fetch afterAddi8.pc afterAddi8PcAligned))
        (.success 0x0000a103) eei2)
    (load :
      environment.responds eei2
        (.memory (.load 8 .word)) (.success value) eei3) :
    Execution.Runs environment initialState eei0
      { effects :=
          [ Request.effect
              (.memory (.fetch initialState.pc initialPcAligned))
              (.success 0x00800093),
            Request.effect
              (.memory (.fetch afterAddi8.pc afterAddi8PcAligned))
              (.success 0x0000a103),
            Request.effect (.memory (.load 8 .word)) (.success value) ]
        results := [.retired afterAddi8, .retired (afterLw value)] }
      .prefix (afterLw value) eei3 := by
  have addiRuns :
      Interaction.Runs environment
        (Decoder.fetchDecodeExecute initialState initialPcAligned) eei0
        [Request.effect
          (.memory (.fetch initialState.pc initialPcAligned))
          (.success 0x00800093)]
        (.retired afterAddi8) eei1 := by
    exact Interaction.Runs.request eei0 eei1 eei1
      (.memory (.fetch initialState.pc initialPcAligned))
      (.success 0x00800093)
      (finishFetch initialState initialPcAligned Decoder.decodeAndExecute)
      [] (.retired afterAddi8) fetchAddi
      (Interaction.Runs.done eei1 (InstructionResult.retired afterAddi8))
  have lwRuns :
      Interaction.Runs environment
        (Decoder.fetchDecodeExecute afterAddi8 afterAddi8PcAligned) eei1
        [ Request.effect
            (.memory (.fetch afterAddi8.pc afterAddi8PcAligned))
            (.success 0x0000a103),
          Request.effect (.memory (.load 8 .word)) (.success value) ]
        (.retired (afterLw value)) eei3 := by
    exact Interaction.Runs.request eei1 eei2 eei3
      (.memory (.fetch afterAddi8.pc afterAddi8PcAligned))
      (.success 0x0000a103)
      (finishFetch afterAddi8 afterAddi8PcAligned Decoder.decodeAndExecute)
      [Request.effect (.memory (.load 8 .word)) (.success value)]
      (.retired (afterLw value)) fetchLw
      (Interaction.Runs.request eei2 eei3 eei3
        (.memory (.load 8 .word)) (.success value)
        (finishLoad afterAddi8 2 8 .word false) []
        (.retired (afterLw value)) load
        (Interaction.Runs.done eei3
          (InstructionResult.retired (afterLw value))))
  exact Execution.twoRetired addiRuns lwRuns

/-- A rejected fetched word closes the unprivileged segment at a raised
boundary. No trap-entry state or whole-machine termination is inferred. -/
example {environmentState : Type}
    (environment : ExecutionEnvironment environmentState)
    (eei0 eei1 : environmentState)
    (fetchIllegal :
      environment.responds eei0
        (.memory (.fetch initialState.pc initialPcAligned))
        (.success 0x00000000) eei1) :
    Execution.Runs environment initialState eei0
      { effects :=
          [Request.effect
            (.memory (.fetch initialState.pc initialPcAligned))
            (.success 0x00000000)]
        results := [.raised initialState (.illegalInstruction 0x00000000)] }
      (.raised (.illegalInstruction 0x00000000)) initialState eei1 := by
  apply Execution.Runs.raised initialState initialState eei0 eei1
    initialPcAligned _ (.illegalInstruction 0x00000000)
  exact Interaction.Runs.request eei0 eei1 eei1
    (.memory (.fetch initialState.pc initialPcAligned))
    (.success 0x00000000)
    (finishFetch initialState initialPcAligned Decoder.decodeAndExecute)
    [] (InstructionResult.raised initialState (.illegalInstruction 0x00000000)) fetchIllegal
    (Interaction.Runs.done eei1
      (InstructionResult.raised initialState (.illegalInstruction 0x00000000)))

example (decodeAndExecute : Word → State → Interaction InstructionResult) :
    fetchAndExecute initialState initialPcAligned decodeAndExecute =
      .request (.memory (.fetch initialState.pc initialPcAligned))
        (finishFetch initialState initialPcAligned decodeAndExecute) := by
  rfl

example (decodeAndExecute : Word → State → Interaction InstructionResult) :
    finishFetch initialState initialPcAligned decodeAndExecute .accessFault =
      .done (.raised initialState (.instructionAccessFault initialState.pc)) := by
  rfl

example (decodeAndExecute : Word → State → Interaction InstructionResult) :
    finishFetch initialState initialPcAligned decodeAndExecute (.success 0x00000013) =
      decodeAndExecute 0x00000013 initialState := by
  rfl

end RV32I
