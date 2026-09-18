import RV32I.Architecture

namespace RV32I

/-- Fully decoded base-RV32I instructions.

Constructor operands follow assembly order: destination (when present), then
source operands, then the immediate. In particular, `sw rs2, immediate(rs1)`
is represented as `sw rs2 rs1 immediate`.
-/
inductive DecodedInstruction where
  | lui (rd : Register) (immediate : BitVec 20)
  | auipc (rd : Register) (immediate : BitVec 20)
  | addi (rd rs1 : Register) (immediate : BitVec 12)
  | slti (rd rs1 : Register) (immediate : BitVec 12)
  | sltiu (rd rs1 : Register) (immediate : BitVec 12)
  | xori (rd rs1 : Register) (immediate : BitVec 12)
  | ori (rd rs1 : Register) (immediate : BitVec 12)
  | andi (rd rs1 : Register) (immediate : BitVec 12)
  | slli (rd rs1 : Register) (shamt : BitVec 5)
  | srli (rd rs1 : Register) (shamt : BitVec 5)
  | srai (rd rs1 : Register) (shamt : BitVec 5)
  | add (rd rs1 rs2 : Register)
  | sub (rd rs1 rs2 : Register)
  | sll (rd rs1 rs2 : Register)
  | slt (rd rs1 rs2 : Register)
  | sltu (rd rs1 rs2 : Register)
  | xor (rd rs1 rs2 : Register)
  | srl (rd rs1 rs2 : Register)
  | sra (rd rs1 rs2 : Register)
  | or (rd rs1 rs2 : Register)
  | and (rd rs1 rs2 : Register)
  | beq (rs1 rs2 : Register) (immediate : BitVec 13)
  | bne (rs1 rs2 : Register) (immediate : BitVec 13)
  | blt (rs1 rs2 : Register) (immediate : BitVec 13)
  | bge (rs1 rs2 : Register) (immediate : BitVec 13)
  | bltu (rs1 rs2 : Register) (immediate : BitVec 13)
  | bgeu (rs1 rs2 : Register) (immediate : BitVec 13)
  | jal (rd : Register) (immediate : BitVec 21)
  | jalr (rd rs1 : Register) (immediate : BitVec 12)
  | lb (rd rs1 : Register) (immediate : BitVec 12)
  | lh (rd rs1 : Register) (immediate : BitVec 12)
  | lw (rd rs1 : Register) (immediate : BitVec 12)
  | lbu (rd rs1 : Register) (immediate : BitVec 12)
  | lhu (rd rs1 : Register) (immediate : BitVec 12)
  | sb (rs2 rs1 : Register) (immediate : BitVec 12)
  | sh (rs2 rs1 : Register) (immediate : BitVec 12)
  | sw (rs2 rs1 : Register) (immediate : BitVec 12)
  | fence (fence : Fence)
  | ecall
  | ebreak
  deriving DecidableEq, Repr

namespace Instruction

/-- Place a U-type immediate in bits 31:12, with twelve low zero bits. -/
def upperImmediate (immediate : BitVec 20) : Word :=
  immediate ++ 0#12

/-- LUI writes the U-type immediate value directly. -/
def lui (immediate : BitVec 20) : Word :=
  upperImmediate immediate

/-- AUIPC adds the U-type immediate value to the address of the instruction. -/
def auipc (immediate : BitVec 20) (pc : Address) : Word :=
  pc + upperImmediate immediate

/-- Pure ADDI result, following the clean-function style of `riscv-lean`. -/
def addi (immediate : BitVec 12) (rs1Value : Word) : Word :=
  rs1Value + immediate.signExtend 32

def slti (immediate : BitVec 12) (rs1Value : Word) : Word :=
  (BitVec.ofBool (BitVec.slt rs1Value (immediate.signExtend 32))).zeroExtend 32

def sltiu (immediate : BitVec 12) (rs1Value : Word) : Word :=
  (BitVec.ofBool (BitVec.ult rs1Value (immediate.signExtend 32))).zeroExtend 32

def xori (immediate : BitVec 12) (rs1Value : Word) : Word :=
  rs1Value ^^^ immediate.signExtend 32

def ori (immediate : BitVec 12) (rs1Value : Word) : Word :=
  rs1Value ||| immediate.signExtend 32

def andi (immediate : BitVec 12) (rs1Value : Word) : Word :=
  rs1Value &&& immediate.signExtend 32

def slli (shamt : BitVec 5) (rs1Value : Word) : Word := rs1Value <<< shamt
def srli (shamt : BitVec 5) (rs1Value : Word) : Word := rs1Value >>> shamt
def srai (shamt : BitVec 5) (rs1Value : Word) : Word :=
  BitVec.sshiftRight' rs1Value shamt

def add (rs2Value rs1Value : Word) : Word := rs1Value + rs2Value
def sub (rs2Value rs1Value : Word) : Word := rs1Value - rs2Value
def sll (rs2Value rs1Value : Word) : Word :=
  rs1Value <<< rs2Value.extractLsb' 0 5
def slt (rs2Value rs1Value : Word) : Word :=
  (BitVec.ofBool (BitVec.slt rs1Value rs2Value)).zeroExtend 32
def sltu (rs2Value rs1Value : Word) : Word :=
  (BitVec.ofBool (BitVec.ult rs1Value rs2Value)).zeroExtend 32
def xor (rs2Value rs1Value : Word) : Word := rs1Value ^^^ rs2Value
def srl (rs2Value rs1Value : Word) : Word :=
  rs1Value >>> rs2Value.extractLsb' 0 5
def sra (rs2Value rs1Value : Word) : Word :=
  BitVec.sshiftRight' rs1Value (rs2Value.extractLsb' 0 5)
def or (rs2Value rs1Value : Word) : Word := rs1Value ||| rs2Value
def and (rs2Value rs1Value : Word) : Word := rs1Value &&& rs2Value

def beq (rs2Value rs1Value : Word) : Bool := rs1Value == rs2Value
def bne (rs2Value rs1Value : Word) : Bool := rs1Value != rs2Value
def blt (rs2Value rs1Value : Word) : Bool := BitVec.slt rs1Value rs2Value
def bge (rs2Value rs1Value : Word) : Bool := !BitVec.slt rs1Value rs2Value
def bltu (rs2Value rs1Value : Word) : Bool := BitVec.ult rs1Value rs2Value
def bgeu (rs2Value rs1Value : Word) : Bool := !BitVec.ult rs1Value rs2Value

/-- PC-relative target shared by conditional branches and JAL. -/
def pcRelativeTarget {width : Nat} (immediate : BitVec width)
    (pc : Address) : Address :=
  pc + immediate.signExtend 32

/-- JALR adds its signed immediate and then clears target bit zero. -/
def jalrTarget (immediate : BitVec 12) (rs1Value : Word) : Address :=
  (rs1Value + immediate.signExtend 32) &&& 0xfffffffe

/-- Effective address shared by loads and stores. -/
def address (immediate : BitVec 12) (rs1Value : Word) : Address :=
  rs1Value + immediate.signExtend 32

/-- Extend the width-indexed value returned by one load to XLEN. The unsigned
flag is ignored for a 32-bit word because the value already has XLEN bits. -/
def loadResult : (width : AccessWidth) → Bool → AccessValue width → Word
  | .byte, unsigned, value =>
      if unsigned then value.zeroExtend 32 else value.signExtend 32
  | .half, unsigned, value =>
      if unsigned then value.zeroExtend 32 else value.signExtend 32
  | .word, _, value => value

/-- Select exactly the low byte lanes transferred by a store. -/
def storeValue (width : AccessWidth) (rs2Value : Word) : AccessValue width :=
  match width with
  | .byte => rs2Value.extractLsb' 0 8
  | .half => rs2Value.extractLsb' 0 16
  | .word => rs2Value

end Instruction

def nextPc (state : State) : Address := state.pc + 4

def finishLoad
    (state : State) (rd : Register) (address : Address)
    (width : AccessWidth) (unsigned : Bool)
    (response : (MemoryRequest.load address width).Response) : Interaction InstructionResult :=
  match response with
  | .success value =>
      let nextState :=
        { state.writeRegister rd (Instruction.loadResult width unsigned value) with
          pc := nextPc state }
      .done (.retired nextState)
  | .accessFault => .done (.raised state (.loadAccessFault address))
  | .addressMisaligned _ => .done (.raised state (.loadAddressMisaligned address))

def finishStore
    (state : State) (address : Address) (width : AccessWidth)
    (value : AccessValue width)
    (response : (MemoryRequest.store address width value).Response) : Interaction InstructionResult :=
  match response with
  | .success _ => .done (.retired { state with pc := nextPc state })
  | .accessFault => .done (.raised state (.storeAccessFault address))
  | .addressMisaligned _ => .done (.raised state (.storeAddressMisaligned address))

/-- A fence retires only after the EEI acknowledges its distinct ordering
action. It is not represented as a memory access or silently erased. -/
def finishFence (state : State) (f : Fence)
    (_response : (Request.fence f).Response) : Interaction InstructionResult :=
  .done (.retired { state with pc := nextPc state })

@[simp] theorem finishFence_pc (state : State) (f : Fence) :
    finishFence state f () =
      .done (.retired { state with pc := nextPc state }) := by
  rfl

/-- Successful FENCE acknowledgement advances only the PC; every integer
register read is preserved. -/
theorem finishFence_preserves_registers (state : State) (_f : Fence)
    (register : Register) :
    ({ state with pc := nextPc state } : State).readRegister register =
      state.readRegister register := by
  rfl

/-- Complete a taken control transfer. With IALIGN=32, a target whose low two
bits are not zero raises at the original state. The caller supplies any link
write only on the aligned path. -/
def finishJump (state successState : State) (target : Address) :
    Interaction InstructionResult :=
  if target.toNat % 4 = 0 then
    .done (.retired { successState with pc := target })
  else
    .done (.raised state (.instructionAddressMisaligned target))

def executeBranch (state : State) (taken : Bool) (immediate : BitVec 13) :
    Interaction InstructionResult :=
  if taken then
    let target := Instruction.pcRelativeTarget immediate state.pc
    finishJump state state target
  else
    .done (.retired { state with pc := nextPc state })

@[simp] theorem finishJump_aligned (state successState : State)
    (target : Address) (aligned : target.toNat % 4 = 0) :
    finishJump state successState target =
      .done (.retired { successState with pc := target }) := by
  simp [finishJump, aligned]

@[simp] theorem finishJump_misaligned (state successState : State)
    (target : Address) (misaligned : target.toNat % 4 ≠ 0) :
    finishJump state successState target =
      .done (.raised state (.instructionAddressMisaligned target)) := by
  simp [finishJump, misaligned]

@[simp] theorem executeBranch_notTaken (state : State)
    (immediate : BitVec 13) :
    executeBranch state false immediate =
      .done (.retired { state with pc := nextPc state }) := by
  rfl

/-- A failed control transfer exposes the attempted target and preserves the
entire faulting state, including the would-be link register. -/
theorem finishJump_failure_preserves_state (state successState : State)
    (target : Address) (misaligned : target.toNat % 4 ≠ 0) :
    finishJump state successState target =
      .done (.raised state (.instructionAddressMisaligned target)) :=
  finishJump_misaligned state successState target misaligned

/-- Execute one decoded base-RV32I instruction.

Every register-only computation completes immediately. Loads and stores
suspend at a typed memory request; their continuations consume only a response
appropriate to that request. Alignment policy and access validity therefore
belong to the EEI without introducing irrelevant memory inputs for
register-only instructions.
-/
def execute : DecodedInstruction → State → Interaction InstructionResult
  | .lui rd immediate, state =>
      let nextState :=
        { state.writeRegister rd (Instruction.lui immediate) with
          pc := nextPc state }
      .done (.retired nextState)
  | .auipc rd immediate, state =>
      let nextState :=
        { state.writeRegister rd (Instruction.auipc immediate state.pc) with
          pc := nextPc state }
      .done (.retired nextState)
  | .addi rd rs1 immediate, state =>
      let value := Instruction.addi immediate (state.readRegister rs1)
      let nextState := { state.writeRegister rd value with pc := nextPc state }
      .done (.retired nextState)
  | .slti rd rs1 immediate, state =>
      .done (.retired { state.writeRegister rd
        (Instruction.slti immediate (state.readRegister rs1)) with pc := nextPc state })
  | .sltiu rd rs1 immediate, state =>
      .done (.retired { state.writeRegister rd
        (Instruction.sltiu immediate (state.readRegister rs1)) with pc := nextPc state })
  | .xori rd rs1 immediate, state =>
      .done (.retired { state.writeRegister rd
        (Instruction.xori immediate (state.readRegister rs1)) with pc := nextPc state })
  | .ori rd rs1 immediate, state =>
      .done (.retired { state.writeRegister rd
        (Instruction.ori immediate (state.readRegister rs1)) with pc := nextPc state })
  | .andi rd rs1 immediate, state =>
      .done (.retired { state.writeRegister rd
        (Instruction.andi immediate (state.readRegister rs1)) with pc := nextPc state })
  | .slli rd rs1 shamt, state =>
      .done (.retired { state.writeRegister rd
        (Instruction.slli shamt (state.readRegister rs1)) with pc := nextPc state })
  | .srli rd rs1 shamt, state =>
      .done (.retired { state.writeRegister rd
        (Instruction.srli shamt (state.readRegister rs1)) with pc := nextPc state })
  | .srai rd rs1 shamt, state =>
      .done (.retired { state.writeRegister rd
        (Instruction.srai shamt (state.readRegister rs1)) with pc := nextPc state })
  | .add rd rs1 rs2, state =>
      .done (.retired { state.writeRegister rd
        (Instruction.add (state.readRegister rs2) (state.readRegister rs1)) with pc := nextPc state })
  | .sub rd rs1 rs2, state =>
      .done (.retired { state.writeRegister rd
        (Instruction.sub (state.readRegister rs2) (state.readRegister rs1)) with pc := nextPc state })
  | .sll rd rs1 rs2, state =>
      .done (.retired { state.writeRegister rd
        (Instruction.sll (state.readRegister rs2) (state.readRegister rs1)) with pc := nextPc state })
  | .slt rd rs1 rs2, state =>
      .done (.retired { state.writeRegister rd
        (Instruction.slt (state.readRegister rs2) (state.readRegister rs1)) with pc := nextPc state })
  | .sltu rd rs1 rs2, state =>
      .done (.retired { state.writeRegister rd
        (Instruction.sltu (state.readRegister rs2) (state.readRegister rs1)) with pc := nextPc state })
  | .xor rd rs1 rs2, state =>
      .done (.retired { state.writeRegister rd
        (Instruction.xor (state.readRegister rs2) (state.readRegister rs1)) with pc := nextPc state })
  | .srl rd rs1 rs2, state =>
      .done (.retired { state.writeRegister rd
        (Instruction.srl (state.readRegister rs2) (state.readRegister rs1)) with pc := nextPc state })
  | .sra rd rs1 rs2, state =>
      .done (.retired { state.writeRegister rd
        (Instruction.sra (state.readRegister rs2) (state.readRegister rs1)) with pc := nextPc state })
  | .or rd rs1 rs2, state =>
      .done (.retired { state.writeRegister rd
        (Instruction.or (state.readRegister rs2) (state.readRegister rs1)) with pc := nextPc state })
  | .and rd rs1 rs2, state =>
      .done (.retired { state.writeRegister rd
        (Instruction.and (state.readRegister rs2) (state.readRegister rs1)) with pc := nextPc state })
  | .beq rs1 rs2 immediate, state =>
      executeBranch state (Instruction.beq (state.readRegister rs2) (state.readRegister rs1)) immediate
  | .bne rs1 rs2 immediate, state =>
      executeBranch state (Instruction.bne (state.readRegister rs2) (state.readRegister rs1)) immediate
  | .blt rs1 rs2 immediate, state =>
      executeBranch state (Instruction.blt (state.readRegister rs2) (state.readRegister rs1)) immediate
  | .bge rs1 rs2 immediate, state =>
      executeBranch state (Instruction.bge (state.readRegister rs2) (state.readRegister rs1)) immediate
  | .bltu rs1 rs2 immediate, state =>
      executeBranch state (Instruction.bltu (state.readRegister rs2) (state.readRegister rs1)) immediate
  | .bgeu rs1 rs2 immediate, state =>
      executeBranch state (Instruction.bgeu (state.readRegister rs2) (state.readRegister rs1)) immediate
  | .jal rd immediate, state =>
      let target := Instruction.pcRelativeTarget immediate state.pc
      finishJump state (state.writeRegister rd (nextPc state)) target
  | .jalr rd rs1 immediate, state =>
      let target := Instruction.jalrTarget immediate (state.readRegister rs1)
      finishJump state (state.writeRegister rd (nextPc state)) target
  | .lb rd rs1 immediate, state =>
      let address := Instruction.address immediate (state.readRegister rs1)
      .request (.memory (.load address .byte))
        (finishLoad state rd address .byte false)
  | .lh rd rs1 immediate, state =>
      let address := Instruction.address immediate (state.readRegister rs1)
      .request (.memory (.load address .half))
        (finishLoad state rd address .half false)
  | .lw rd rs1 immediate, state =>
      let address := Instruction.address immediate (state.readRegister rs1)
      .request (.memory (.load address .word))
        (finishLoad state rd address .word false)
  | .lbu rd rs1 immediate, state =>
      let address := Instruction.address immediate (state.readRegister rs1)
      .request (.memory (.load address .byte))
        (finishLoad state rd address .byte true)
  | .lhu rd rs1 immediate, state =>
      let address := Instruction.address immediate (state.readRegister rs1)
      .request (.memory (.load address .half))
        (finishLoad state rd address .half true)
  | .sb rs2 rs1 immediate, state =>
      let address := Instruction.address immediate (state.readRegister rs1)
      let value := Instruction.storeValue .byte (state.readRegister rs2)
      .request (.memory (.store address .byte value))
        (finishStore state address .byte value)
  | .sh rs2 rs1 immediate, state =>
      let address := Instruction.address immediate (state.readRegister rs1)
      let value := Instruction.storeValue .half (state.readRegister rs2)
      .request (.memory (.store address .half value))
        (finishStore state address .half value)
  | .sw rs2 rs1 immediate, state =>
      let address := Instruction.address immediate (state.readRegister rs1)
      let value := Instruction.storeValue .word (state.readRegister rs2)
      .request (.memory (.store address .word value))
        (finishStore state address .word value)
  | .fence f, state =>
      .request (.fence f) (finishFence state f)
  | .ecall, state =>
      .done (.raised state .environmentCall)
  | .ebreak, state =>
      .done (.raised state .breakpoint)

@[simp] theorem execute_ecall (state : State) :
    execute .ecall state = .done (.raised state .environmentCall) := by
  rfl

@[simp] theorem execute_ebreak (state : State) :
    execute .ebreak state = .done (.raised state .breakpoint) := by
  rfl

/-- Consume the response to an aligned instruction-fetch request. -/
def finishFetch (state : State) (aligned : state.pc.toNat % 4 = 0)
    (decodeAndExecute : Word → State → Interaction InstructionResult)
    (response : (MemoryRequest.fetch state.pc aligned).Response) :
    Interaction InstructionResult :=
  match response with
  | .success instruction => decodeAndExecute instruction state
  | .accessFault => .done (.raised state (.instructionAccessFault state.pc))

/-- Fetch and execute one instruction using a supplied decoder/executor.

The callback keeps decoding separate from instruction semantics. With
IALIGN=32, the caller supplies the aligned-PC invariant. Branch and jump semantics are
responsible for raising instruction-address-misaligned before producing a bad
successor PC. A valid fetch may still receive an instruction access fault.
-/
def fetchAndExecute (state : State) (aligned : state.pc.toNat % 4 = 0)
    (decodeAndExecute : Word → State → Interaction InstructionResult) :
    Interaction InstructionResult :=
  .request (.memory (.fetch state.pc aligned))
    (finishFetch state aligned decodeAndExecute)

@[simp] theorem finishLoad_accessFault
    (state : State) (rd : Register) (address : Address)
    (width : AccessWidth) (unsigned : Bool) :
    finishLoad state rd address width unsigned .accessFault =
      .done (.raised state (.loadAccessFault address)) := by
  rfl

@[simp] theorem finishLoad_success
    (state : State) (rd : Register) (address : Address)
    (width : AccessWidth) (unsigned : Bool) (value : AccessValue width) :
    finishLoad state rd address width unsigned (.success value) =
      .done (.retired
        { state.writeRegister rd (Instruction.loadResult width unsigned value) with
          pc := nextPc state }) := by
  rfl

@[simp] theorem finishLoad_success_zero
    (state : State) (address : Address)
    (width : AccessWidth) (unsigned : Bool) (value : AccessValue width) :
    finishLoad state 0 address width unsigned (.success value) =
      .done (.retired { state with pc := nextPc state }) := by
  simp [finishLoad]

@[simp] theorem finishStore_accessFault
    (state : State) (address : Address) (width : AccessWidth)
    (value : AccessValue width) :
    finishStore state address width value .accessFault =
      .done (.raised state (.storeAccessFault address)) := by
  rfl

@[simp] theorem finishStore_success
    (state : State) (address : Address) (width : AccessWidth)
    (value : AccessValue width) :
    finishStore state address width value (.success ()) =
      .done (.retired { state with pc := nextPc state }) := by
  rfl

@[simp] theorem finishLoad_addressMisaligned
    (state : State) (rd : Register) (address : Address)
    (width : AccessWidth) (unsigned : Bool)
    (misaligned : ¬ width.Aligned address) :
    finishLoad state rd address width unsigned (.addressMisaligned misaligned) =
      .done (.raised state (.loadAddressMisaligned address)) := by
  rfl

@[simp] theorem finishStore_addressMisaligned
    (state : State) (address : Address) (width : AccessWidth)
    (value : AccessValue width) (misaligned : ¬ width.Aligned address) :
    finishStore state address width value (.addressMisaligned misaligned) =
      .done (.raised state (.storeAddressMisaligned address)) := by
  rfl

@[simp] theorem finishFetch_accessFault
    (state : State) (aligned : state.pc.toNat % 4 = 0)
    (decodeAndExecute : Word → State → Interaction InstructionResult) :
    finishFetch state aligned decodeAndExecute .accessFault =
      .done (.raised state (.instructionAccessFault state.pc)) := by
  rfl

/-- Discarding a loaded value through `x0` does not discard the access. -/
theorem execute_lw_zero
    (state : State) (rs1 : Register) (immediate : BitVec 12) :
    execute (.lw 0 rs1 immediate) state =
      let address := Instruction.address immediate (state.readRegister rs1)
      .request (.memory (.load address .word))
        (finishLoad state 0 address .word false) := by
  rfl

@[simp] theorem execute_lui_zero
    (state : State) (immediate : BitVec 20) :
    execute (.lui 0 immediate) state =
      .done (.retired { state with pc := nextPc state }) := by
  simp [execute]

@[simp] theorem execute_auipc_zero
    (state : State) (immediate : BitVec 20) :
    execute (.auipc 0 immediate) state =
      .done (.retired { state with pc := nextPc state }) := by
  simp [execute]

end RV32I
