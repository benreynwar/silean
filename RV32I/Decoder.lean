import RV32I.Instructions

namespace RV32I

namespace Decoder

/-- The seven-bit major opcode in bits 6:0. -/
def opcode (instruction : Word) : BitVec 7 :=
  instruction.extractLsb' 0 7

/-- The destination register in bits 11:7. -/
def rd (instruction : Word) : Register :=
  (instruction.extractLsb' 7 5).toFin

/-- The three-bit minor opcode in bits 14:12. -/
def funct3 (instruction : Word) : BitVec 3 :=
  instruction.extractLsb' 12 3

/-- The seven-bit minor opcode in bits 31:25. -/
def funct7 (instruction : Word) : BitVec 7 :=
  instruction.extractLsb' 25 7

/-- The first source register in bits 19:15. -/
def rs1 (instruction : Word) : Register :=
  (instruction.extractLsb' 15 5).toFin

/-- The second source register in bits 24:20. -/
def rs2 (instruction : Word) : Register :=
  (instruction.extractLsb' 20 5).toFin

/-- The I-type immediate in bits 31:20. It remains a 12-bit two's-complement
value until instruction execution sign-extends it to XLEN. -/
def iImmediate (instruction : Word) : BitVec 12 :=
  instruction.extractLsb' 20 12

/-- Reconstruct the S-type immediate as `instruction[31:25] ++
instruction[11:7]`. It remains a 12-bit two's-complement value until use. -/
def sImmediate (instruction : Word) : BitVec 12 :=
  instruction.extractLsb' 25 7 ++ instruction.extractLsb' 7 5

/-- The U-type immediate in bits 31:12. Its twelve low zero bits are appended
when LUI or AUIPC evaluates the instruction. -/
def uImmediate (instruction : Word) : BitVec 20 :=
  instruction.extractLsb' 12 20

/-- Reconstruct B-immediate bits `12|11|10:5|4:1|0`. The encoded low bit is
implicit and therefore restored as zero. -/
def bImmediate (instruction : Word) : BitVec 13 :=
  instruction.extractLsb' 31 1 ++ instruction.extractLsb' 7 1 ++
    instruction.extractLsb' 25 6 ++ instruction.extractLsb' 8 4 ++ 0#1

/-- Reconstruct J-immediate bits `20|19:12|11|10:1|0`. -/
def jImmediate (instruction : Word) : BitVec 21 :=
  instruction.extractLsb' 31 1 ++ instruction.extractLsb' 12 8 ++
    instruction.extractLsb' 20 1 ++ instruction.extractLsb' 21 10 ++ 0#1

/-- FENCE predecessor bits in architectural `IORW` order. -/
def fencePredecessor (instruction : Word) : FenceSet :=
  FenceSet.ofBits (instruction.extractLsb' 24 4)

/-- FENCE successor bits in architectural `IORW` order. -/
def fenceSuccessor (instruction : Word) : FenceSet :=
  FenceSet.ofBits (instruction.extractLsb' 20 4)

/-- The one distinguished FENCE.TSO encoding. The unused `rs1` and `rd`
fields must both be zero for this configuration; other configurations with
`fm=1000` are reserved and base implementations treat them as normal FENCE. -/
def isFenceTso (instruction : Word) : Bool :=
  instruction == 0x8330000f

/-- The base SYSTEM subdecoder. Base RV32I contains exactly ECALL and EBREAK;
all CSR, counter, return-from-trap, wait, and extension encodings remain
outside this datatype. -/
def decodeSystem (instruction : Word) : Option DecodedInstruction :=
  if instruction == 0x00000073 then
    some .ecall
  else if instruction == 0x00100073 then
    some .ebreak
  else
    none

@[simp] theorem decodeSystem_ecall :
    decodeSystem 0x00000073 = some .ecall := by
  rfl

@[simp] theorem decodeSystem_ebreak :
    decodeSystem 0x00100073 = some .ebreak := by
  rfl

theorem decodeSystem_eq_some_iff (instruction : Word)
    (decoded : DecodedInstruction) :
    decodeSystem instruction = some decoded ↔
      (instruction = 0x00000073 ∧ decoded = .ecall) ∨
      (instruction = 0x00100073 ∧ decoded = .ebreak) := by
  constructor
  · intro decoded_eq
    by_cases isEcall : instruction == 0x00000073
    · left
      have instruction_eq : instruction = 0x00000073 := beq_iff_eq.mp isEcall
      simp only [decodeSystem, isEcall, ↓reduceIte, Option.some.injEq] at decoded_eq
      exact ⟨instruction_eq, decoded_eq.symm⟩
    · by_cases isEbreak : instruction == 0x00100073
      · right
        have instruction_eq : instruction = 0x00100073 := beq_iff_eq.mp isEbreak
        simp only [decodeSystem, isEcall, isEbreak, Bool.false_eq_true,
          ↓reduceIte, Option.some.injEq] at decoded_eq
        exact ⟨instruction_eq, decoded_eq.symm⟩
      · have notEcall : instruction ≠ 0x00000073 := by
          intro instruction_eq
          exact isEcall (beq_iff_eq.mpr instruction_eq)
        have notEbreak : instruction ≠ 0x00100073 := by
          intro instruction_eq
          exact isEbreak (beq_iff_eq.mpr instruction_eq)
        simp only [decodeSystem, beq_iff_eq] at decoded_eq
        rw [if_neg notEcall, if_neg notEbreak] at decoded_eq
        contradiction
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl

/-- Decode exactly the base RV32I instruction set.

LUI and AUIPC use the whole bits 31:12 field as their U-immediate. All OP-IMM
and OP instructions check their required minor opcodes, including the exact
RV32 shift upper bits. Branches and jumps reconstruct their scattered signed
immediates, and JALR checks its required `funct3`. The LOAD and STORE opcodes
accept exactly the five and three RV32I `funct3` values. MISC-MEM with
`funct3=000` recognizes exact FENCE.TSO first and otherwise decodes a normal
FENCE, including reserved configurations as required by the base ISA. The
`funct3=001` FENCE.I extension remains rejected. SYSTEM recognizes only the
exact ECALL and EBREAK words; CSR, counter, privileged, and extension words
remain rejected. Every other word is illegal in this base-only model. -/
def decode (instruction : Word) : Option DecodedInstruction :=
  match (opcode instruction).toNat, (funct3 instruction).toNat,
      (funct7 instruction).toNat with
  | 0b0110111, _, _ =>
      some (.lui (rd instruction) (uImmediate instruction))
  | 0b0010111, _, _ =>
      some (.auipc (rd instruction) (uImmediate instruction))
  | 0b1101111, _, _ =>
      some (.jal (rd instruction) (jImmediate instruction))
  | 0b1100111, 0b000, _ =>
      some (.jalr (rd instruction) (rs1 instruction) (iImmediate instruction))
  | 0b1100011, 0b000, _ =>
      some (.beq (rs1 instruction) (rs2 instruction) (bImmediate instruction))
  | 0b1100011, 0b001, _ =>
      some (.bne (rs1 instruction) (rs2 instruction) (bImmediate instruction))
  | 0b1100011, 0b100, _ =>
      some (.blt (rs1 instruction) (rs2 instruction) (bImmediate instruction))
  | 0b1100011, 0b101, _ =>
      some (.bge (rs1 instruction) (rs2 instruction) (bImmediate instruction))
  | 0b1100011, 0b110, _ =>
      some (.bltu (rs1 instruction) (rs2 instruction) (bImmediate instruction))
  | 0b1100011, 0b111, _ =>
      some (.bgeu (rs1 instruction) (rs2 instruction) (bImmediate instruction))
  | 0b0010011, 0b000, _ =>
      some (.addi (rd instruction) (rs1 instruction) (iImmediate instruction))
  | 0b0010011, 0b010, _ =>
      some (.slti (rd instruction) (rs1 instruction) (iImmediate instruction))
  | 0b0010011, 0b011, _ =>
      some (.sltiu (rd instruction) (rs1 instruction) (iImmediate instruction))
  | 0b0010011, 0b100, _ =>
      some (.xori (rd instruction) (rs1 instruction) (iImmediate instruction))
  | 0b0010011, 0b110, _ =>
      some (.ori (rd instruction) (rs1 instruction) (iImmediate instruction))
  | 0b0010011, 0b111, _ =>
      some (.andi (rd instruction) (rs1 instruction) (iImmediate instruction))
  | 0b0010011, 0b001, 0b0000000 =>
      some (.slli (rd instruction) (rs1 instruction)
        (instruction.extractLsb' 20 5))
  | 0b0010011, 0b101, 0b0000000 =>
      some (.srli (rd instruction) (rs1 instruction)
        (instruction.extractLsb' 20 5))
  | 0b0010011, 0b101, 0b0100000 =>
      some (.srai (rd instruction) (rs1 instruction)
        (instruction.extractLsb' 20 5))
  | 0b0110011, 0b000, 0b0000000 => some (.add (rd instruction) (rs1 instruction) (rs2 instruction))
  | 0b0110011, 0b000, 0b0100000 => some (.sub (rd instruction) (rs1 instruction) (rs2 instruction))
  | 0b0110011, 0b001, 0b0000000 => some (.sll (rd instruction) (rs1 instruction) (rs2 instruction))
  | 0b0110011, 0b010, 0b0000000 => some (.slt (rd instruction) (rs1 instruction) (rs2 instruction))
  | 0b0110011, 0b011, 0b0000000 => some (.sltu (rd instruction) (rs1 instruction) (rs2 instruction))
  | 0b0110011, 0b100, 0b0000000 => some (.xor (rd instruction) (rs1 instruction) (rs2 instruction))
  | 0b0110011, 0b101, 0b0000000 => some (.srl (rd instruction) (rs1 instruction) (rs2 instruction))
  | 0b0110011, 0b101, 0b0100000 => some (.sra (rd instruction) (rs1 instruction) (rs2 instruction))
  | 0b0110011, 0b110, 0b0000000 => some (.or (rd instruction) (rs1 instruction) (rs2 instruction))
  | 0b0110011, 0b111, 0b0000000 => some (.and (rd instruction) (rs1 instruction) (rs2 instruction))
  | 0b0000011, 0b000, _ =>
      some (.lb (rd instruction) (rs1 instruction) (iImmediate instruction))
  | 0b0000011, 0b001, _ =>
      some (.lh (rd instruction) (rs1 instruction) (iImmediate instruction))
  | 0b0000011, 0b010, _ =>
      some (.lw (rd instruction) (rs1 instruction) (iImmediate instruction))
  | 0b0000011, 0b100, _ =>
      some (.lbu (rd instruction) (rs1 instruction) (iImmediate instruction))
  | 0b0000011, 0b101, _ =>
      some (.lhu (rd instruction) (rs1 instruction) (iImmediate instruction))
  | 0b0100011, 0b000, _ =>
      some (.sb (rs2 instruction) (rs1 instruction) (sImmediate instruction))
  | 0b0100011, 0b001, _ =>
      some (.sh (rs2 instruction) (rs1 instruction) (sImmediate instruction))
  | 0b0100011, 0b010, _ =>
      some (.sw (rs2 instruction) (rs1 instruction) (sImmediate instruction))
  | 0b0001111, 0b000, _ =>
      if isFenceTso instruction then
        some (.fence .tso)
      else
        some (.fence (.normal (fencePredecessor instruction)
          (fenceSuccessor instruction)))
  | 0b1110011, 0b000, _ =>
      decodeSystem instruction
  | _, _, _ => none

@[simp] theorem decode_ecall : decode 0x00000073 = some .ecall := by
  rfl

@[simp] theorem decode_ebreak : decode 0x00100073 = some .ebreak := by
  rfl

/-- Execute a decoded instruction, or raise illegal-instruction at the
faulting state when this decoder rejects the word. -/
def decodeAndExecute (instruction : Word) (state : State) :
    Interaction InstructionResult :=
  match decode instruction with
  | some decoded => execute decoded state
  | none => .done (.raised state (.illegalInstruction instruction))

/-- Fetch, decode, and execute one base-RV32I instruction. -/
def fetchDecodeExecute (state : State) (aligned : state.pc.toNat % 4 = 0) :
    Interaction InstructionResult :=
  fetchAndExecute state aligned decodeAndExecute

@[simp] theorem decodeAndExecute_decoded
    (instruction : Word) (state : State) (decoded : DecodedInstruction)
    (decoded_eq : decode instruction = some decoded) :
    decodeAndExecute instruction state = execute decoded state := by
  simp [decodeAndExecute, decoded_eq]

/-- Because decoding is a pure function, a word has at most one decoder
result. -/
theorem deterministic (instruction : Word)
    {left right : Option DecodedInstruction}
    (left_eq : decode instruction = left)
    (right_eq : decode instruction = right) :
    left = right := by
  rw [← left_eq, ← right_eq]

@[simp] theorem decodeAndExecute_illegal (instruction : Word) (state : State)
    (illegal : decode instruction = none) :
    decodeAndExecute instruction state =
      .done (.raised state (.illegalInstruction instruction)) := by
  simp [decodeAndExecute, illegal]

end Decoder

end RV32I
