import SailBridge.Memory
import Std.Data.ExtDHashMap.Lemmas
import Std.Data.ExtHashMap.Lemmas

/-!
This module is the dependency boundary between the clean RV32I model and the
generated Lean translation of the Sail RISC-V model. Generated names and
proof-oriented adapters belong here, never in the public `RV32I` library.
-/

namespace RV32I.SailBridge

open LeanRV32D.Functions
open Sail.ConcurrencyInterfaceV1

/-- The sequential state used by the generated Sail monad. This alias is
bridge-only: the public model deliberately does not expose generated state. -/
abbrev SailState :=
  SequentialState LeanRV32D.RegisterType trivialChoiceSource

/-- Reinterpret a clean architectural register number as Sail's generated
five-bit register index. -/
def sailRegister (register : RV32I.Register) : LeanRV32D.regidx :=
  .Regidx (BitVec.ofNat 5 register.val)

/-- A generated x-register key together with the fact that the dependently
typed generated register map stores a 32-bit word at that key. -/
structure SailXKey where
  key : LeanRV32D.Register
  wordType : LeanRV32D.RegisterType key = RV32I.Word

def sailReadKey (sail : SailState) (key : SailXKey) : Option RV32I.Word :=
  (sail.regs.get? key.key).map (cast key.wordType)

def sailWriteKey (sail : SailState) (key : SailXKey)
    (value : RV32I.Word) : SailState :=
  { sail with
    regs := sail.regs.insert key.key (cast key.wordType.symm value) }

/-- Map a nonzero architectural register number to its generated x-register
state key. The x0 case is an unused default because x0 is not stored. -/
def sailXKey (register : RV32I.Register) : SailXKey :=
  match register.val with
  | 0 | 1 => ⟨.x1, rfl⟩
  | 2 => ⟨.x2, rfl⟩
  | 3 => ⟨.x3, rfl⟩
  | 4 => ⟨.x4, rfl⟩
  | 5 => ⟨.x5, rfl⟩
  | 6 => ⟨.x6, rfl⟩
  | 7 => ⟨.x7, rfl⟩
  | 8 => ⟨.x8, rfl⟩
  | 9 => ⟨.x9, rfl⟩
  | 10 => ⟨.x10, rfl⟩
  | 11 => ⟨.x11, rfl⟩
  | 12 => ⟨.x12, rfl⟩
  | 13 => ⟨.x13, rfl⟩
  | 14 => ⟨.x14, rfl⟩
  | 15 => ⟨.x15, rfl⟩
  | 16 => ⟨.x16, rfl⟩
  | 17 => ⟨.x17, rfl⟩
  | 18 => ⟨.x18, rfl⟩
  | 19 => ⟨.x19, rfl⟩
  | 20 => ⟨.x20, rfl⟩
  | 21 => ⟨.x21, rfl⟩
  | 22 => ⟨.x22, rfl⟩
  | 23 => ⟨.x23, rfl⟩
  | 24 => ⟨.x24, rfl⟩
  | 25 => ⟨.x25, rfl⟩
  | 26 => ⟨.x26, rfl⟩
  | 27 => ⟨.x27, rfl⟩
  | 28 => ⟨.x28, rfl⟩
  | 29 => ⟨.x29, rfl⟩
  | 30 => ⟨.x30, rfl⟩
  | _ => ⟨.x31, rfl⟩

/-- Read the integer-register portion of a generated sequential state. Sail
does not store x0; nonzero registers use the typed x1--x31 key adapter. -/
def sailReadX (sail : SailState) (r : RV32I.Register) : Option RV32I.Word :=
  if h : r.val = 0 then some 0
  else sailReadKey sail (sailXKey r)

/-- The generated state update performed by an integer-register write, after
the generated no-op callback has been normalized away. -/
def sailWriteX (sail : SailState) (r : RV32I.Register)
    (value : RV32I.Word) : SailState :=
  if h : r.val = 0 then sail
  else sailWriteKey sail (sailXKey r) value

/-- Exhaustiveness principle used only to normalize generated 32-way register
matches. -/
theorem register_cases (r : RV32I.Register) :
    r.val = 0 ∨
      r.val = 1 ∨
      r.val = 2 ∨
      r.val = 3 ∨
      r.val = 4 ∨
      r.val = 5 ∨
      r.val = 6 ∨
      r.val = 7 ∨
      r.val = 8 ∨
      r.val = 9 ∨
      r.val = 10 ∨
      r.val = 11 ∨
      r.val = 12 ∨
      r.val = 13 ∨
      r.val = 14 ∨
      r.val = 15 ∨
      r.val = 16 ∨
      r.val = 17 ∨
      r.val = 18 ∨
      r.val = 19 ∨
      r.val = 20 ∨
      r.val = 21 ∨
      r.val = 22 ∨
      r.val = 23 ∨
      r.val = 24 ∨
      r.val = 25 ∨
      r.val = 26 ∨
      r.val = 27 ∨
      r.val = 28 ∨
      r.val = 29 ∨
      r.val = 30 ∨
      r.val = 31 := by
  have bound := r.isLt
  omega

theorem sailReadKey_write_same (sail : SailState) (key : SailXKey)
    (value : RV32I.Word) :
    sailReadKey (sailWriteKey sail key value) key = some value := by
  simp [sailReadKey, sailWriteKey]

theorem sailReadKey_write_ne (sail : SailState)
    (written observed : SailXKey) (value : RV32I.Word)
    (different : observed.key ≠ written.key) :
    sailReadKey (sailWriteKey sail written value) observed =
      sailReadKey sail observed := by
  have reversed : written.key ≠ observed.key := Ne.symm different
  simp [sailReadKey, sailWriteKey, Std.ExtDHashMap.get?_insert, reversed]

def sailXKeyNumber : LeanRV32D.Register → Nat
  | .x1 => 1
  | .x2 => 2
  | .x3 => 3
  | .x4 => 4
  | .x5 => 5
  | .x6 => 6
  | .x7 => 7
  | .x8 => 8
  | .x9 => 9
  | .x10 => 10
  | .x11 => 11
  | .x12 => 12
  | .x13 => 13
  | .x14 => 14
  | .x15 => 15
  | .x16 => 16
  | .x17 => 17
  | .x18 => 18
  | .x19 => 19
  | .x20 => 20
  | .x21 => 21
  | .x22 => 22
  | .x23 => 23
  | .x24 => 24
  | .x25 => 25
  | .x26 => 26
  | .x27 => 27
  | .x28 => 28
  | .x29 => 29
  | .x30 => 30
  | .x31 => 31
  | _ => 0

theorem sailXKeyNumber_sailXKey (r : RV32I.Register)
    (nonzero : r.val ≠ 0) : sailXKeyNumber (sailXKey r).key = r.val := by
  rcases register_cases r with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals simp_all [sailXKey, sailXKeyNumber]

theorem sailXKey_of_nonzero_injective {r s : RV32I.Register}
    (rNonzero : r.val ≠ 0) (sNonzero : s.val ≠ 0)
    (equal : (sailXKey r).key = (sailXKey s).key) : r = s := by
  apply Fin.ext
  have numbersEqual := congrArg sailXKeyNumber equal
  rw [sailXKeyNumber_sailXKey r rNonzero,
    sailXKeyNumber_sailXKey s sNonzero] at numbersEqual
  exact numbersEqual

/-- Observable correspondence before an instruction: the clean PC agrees
with Sail's architectural `PC`, and all architectural integer-register reads
agree. In particular this includes the generated model's hard-wired x0 read. -/
structure StateCorresponds (clean : RV32I.State) (sail : SailState) : Prop where
  pc : sail.regs.get? LeanRV32D.Register.PC = some clean.pc
  register : ∀ r : RV32I.Register,
    sailReadX sail r = some (clean.readRegister r)

/-- Update one generated register while preserving every unrelated component
of generated sequential state. -/
def sailSetReg (sail : SailState) (r : LeanRV32D.Register)
    (value : LeanRV32D.RegisterType r) : SailState :=
  { sail with regs := sail.regs.insert r value }

/-- Correspondence after Sail has staged the sequential successor in
`nextPC`, but before its later `tick_pc` commits that value to `PC`. -/
structure StagedStateCorresponds (clean : RV32I.State)
    (sail : SailState) : Prop where
  pc : sail.regs.get? LeanRV32D.Register.PC = some clean.pc
  nextPc : sail.regs.get? LeanRV32D.Register.nextPC =
    some (RV32I.nextPc clean)
  register : ∀ r : RV32I.Register,
    sailReadX sail r = some (clean.readRegister r)

theorem writeReg_eq_set (sail : SailState) (r : LeanRV32D.Register)
    (value : LeanRV32D.RegisterType r) :
    LeanRV32D.writeReg r value sail = .ok () (sailSetReg sail r value) := by
  simp [LeanRV32D.writeReg, PreSail.writeReg, sailSetReg, modify]
  rfl

theorem readReg_of_get {sail : SailState} {r : LeanRV32D.Register}
    {value : LeanRV32D.RegisterType r}
    (found : sail.regs.get? r = some value) :
    LeanRV32D.readReg r sail = .ok value sail := by
  simp [LeanRV32D.readReg, PreSail.readReg, get, getThe,
    MonadStateOf.get, EStateM.get, bind, EStateM.bind, found]
  rfl

theorem rX_bits_of_corresponds {clean : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds clean sail) (r : RV32I.Register) :
    rX_bits (sailRegister r) sail =
      .ok (clean.readRegister r) sail := by
  have observed := corresponds.register r
  rcases register_cases r with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals try simp only [sailReadX, h, dif_pos, dif_neg] at observed
  all_goals try simp only [sailXKey, h] at observed
  all_goals simp [sailReadKey, sailXKey, h] at observed
  all_goals
    simp [rX_bits, rX, sailRegister, Sail.BitVec.toNatInt, h, zero_reg,
      zeros, regval_from_reg, LeanRV32D.readReg, PreSail.readReg,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
      observed]
    rfl

theorem wX_bits_sailRegister (sail : SailState) (r : RV32I.Register)
    (value : RV32I.Word) :
    wX_bits (sailRegister r) value sail =
      .ok () (sailWriteX sail r value) := by
  rcases register_cases r with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals try simp only [sailWriteX, h, dif_pos, dif_neg]
  all_goals try simp only [sailXKey, h]
  all_goals
    simp [wX_bits, wX, sailRegister, sailWriteKey,
      Sail.BitVec.toNatInt, h,
      regval_into_reg, xreg_write_callback, xreg_full_write_callback,
      LeanRV32D.writeReg, PreSail.writeReg, modify, bind, EStateM.bind]
    rfl

def writableIndex (r : RV32I.Register) (_ : r.val ≠ 0) :
    RV32I.WritableRegister :=
  ⟨r.val - 1, by omega⟩

theorem clean_read_after_write (clean : RV32I.State)
    (rd r : RV32I.Register) (value : RV32I.Word) :
    (clean.writeRegister rd value).readRegister r =
      if rd.val = 0 then clean.readRegister r
      else if r = rd then value else clean.readRegister r := by
  by_cases rdZero : rd.val = 0
  · simp [RV32I.State.writeRegister, RV32I.State.readRegister,
      RV32I.Register.writable?, rdZero]
  by_cases rZero : r.val = 0
  · have different : r ≠ rd := by
      intro equal
      subst r
      exact rdZero rZero
    simp [RV32I.State.writeRegister, RV32I.State.readRegister,
      RV32I.Register.writable?, rdZero, rZero, different]
  let rdIndex := writableIndex rd rdZero
  let rIndex := writableIndex r rZero
  have rdWritable : rd.writable? = some rdIndex := by
    simp [RV32I.Register.writable?, rdZero, rdIndex, writableIndex]
  have rWritable : r.writable? = some rIndex := by
    simp [RV32I.Register.writable?, rZero, rIndex, writableIndex]
  by_cases equal : r = rd
  · subst r
    simp [RV32I.State.writeRegister, RV32I.State.readRegister,
      rdWritable, rWritable, rdZero]
  · have indicesDifferent : rIndex ≠ rdIndex := by
      intro indicesEqual
      apply equal
      apply Fin.ext
      have valuesEqual := congrArg Fin.val indicesEqual
      simp [rIndex, rdIndex, writableIndex] at valuesEqual
      omega
    simp only [RV32I.State.writeRegister, rdWritable,
      RV32I.State.readRegister, rWritable, State.registers]
    rw [if_neg rdZero, if_neg equal]
    apply Vector.getElem_set_ne
    intro valuesEqual
    apply indicesDifferent
    apply Fin.ext
    exact valuesEqual.symm

theorem clean_writeRegister_pc (clean : RV32I.State)
    (rd : RV32I.Register) (value : RV32I.Word) :
    (clean.writeRegister rd value).pc = clean.pc := by
  unfold RV32I.State.writeRegister
  split <;> rfl

theorem sail_read_after_write (sail : SailState)
    (rd r : RV32I.Register) (value : RV32I.Word) :
    sailReadX (sailWriteX sail rd value) r =
      if rd.val = 0 then sailReadX sail r
      else if r = rd then some value else sailReadX sail r := by
  by_cases rdZero : rd.val = 0
  · simp [sailWriteX, rdZero]
  by_cases rZero : r.val = 0
  · have different : r ≠ rd := by
      intro equal
      subst r
      exact rdZero rZero
    simp [sailWriteX, sailReadX, rdZero, rZero, different]
  by_cases equal : r = rd
  · subst r
    simp [sailWriteX, sailReadX, rdZero, sailReadKey_write_same]
  · have keysDifferent :
        (sailXKey r).key ≠ (sailXKey rd).key := by
      intro keysEqual
      exact equal (sailXKey_of_nonzero_injective rZero rdZero keysEqual)
    simp [sailWriteX, sailReadX, rdZero, rZero, equal,
      sailReadKey_write_ne, keysDifferent]

theorem sailWriteX_pc (sail : SailState) (rd : RV32I.Register)
    (value : RV32I.Word) :
    (sailWriteX sail rd value).regs.get? LeanRV32D.Register.PC =
      sail.regs.get? LeanRV32D.Register.PC := by
  rcases register_cases rd with hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd
  all_goals try simp only [sailWriteX, hd, dif_pos, dif_neg]
  all_goals try simp only [sailXKey, hd]
  all_goals
    simp [sailWriteKey, hd,
      Std.ExtDHashMap.get?_insert]

theorem StateCorresponds.writeX {clean : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds clean sail) (rd : RV32I.Register)
    (value : RV32I.Word) :
    StateCorresponds (clean.writeRegister rd value)
      (sailWriteX sail rd value) := by
  constructor
  · rw [sailWriteX_pc, clean_writeRegister_pc, corresponds.pc]
  · intro r
    rw [sail_read_after_write, clean_read_after_write]
    by_cases rdZero : rd.val = 0
    · simp [rdZero, corresponds.register r]
    by_cases rEq : r = rd
    · simp [rdZero, rEq]
    · simp [rdZero, rEq, corresponds.register r]

theorem sailReadX_set_nextPc (sail : SailState) (value : RV32I.Word)
    (r : RV32I.Register) :
    sailReadX (sailSetReg sail LeanRV32D.Register.nextPC value) r =
      sailReadX sail r := by
  rcases register_cases r with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals try simp only [sailReadX, h, dif_pos, dif_neg]
  all_goals try simp only [sailXKey, h]
  all_goals
    simp [sailReadKey, sailSetReg, h,
      Std.ExtDHashMap.get?_insert]

theorem sailReadX_set_pc (sail : SailState) (value : RV32I.Word)
    (r : RV32I.Register) :
    sailReadX (sailSetReg sail LeanRV32D.Register.PC value) r =
      sailReadX sail r := by
  rcases register_cases r with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals try simp only [sailReadX, h, dif_pos, dif_neg]
  all_goals try simp only [sailXKey, h]
  all_goals
    simp [sailReadKey, sailSetReg, h,
      Std.ExtDHashMap.get?_insert]

theorem StateCorresponds.stageNextPc {clean : RV32I.State}
    {sail : SailState} (corresponds : StateCorresponds clean sail) :
    StagedStateCorresponds clean
      (sailSetReg sail LeanRV32D.Register.nextPC (RV32I.nextPc clean)) := by
  constructor
  · simpa [sailSetReg, Std.ExtDHashMap.get?_insert] using corresponds.pc
  · simp [sailSetReg, Std.ExtDHashMap.get?_insert]
  · intro r
    rw [sailReadX_set_nextPc]
    exact corresponds.register r

theorem StateCorresponds.setPc {clean : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds clean sail) (value : RV32I.Word) :
    StateCorresponds { clean with pc := value }
      (sailSetReg sail LeanRV32D.Register.PC value) := by
  constructor
  · simp [sailSetReg, Std.ExtDHashMap.get?_insert]
  · intro r
    rw [sailReadX_set_pc]
    exact corresponds.register r

theorem sailWriteX_nextPc (sail : SailState) (rd : RV32I.Register)
    (value : RV32I.Word) :
    (sailWriteX sail rd value).regs.get? LeanRV32D.Register.nextPC =
      sail.regs.get? LeanRV32D.Register.nextPC := by
  rcases register_cases rd with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals try simp only [sailWriteX, h, dif_pos, dif_neg]
  all_goals try simp only [sailXKey, h]
  all_goals
    simp [sailWriteKey, h,
      Std.ExtDHashMap.get?_insert]

theorem tick_pc_of_nextPc {sail : SailState} {value : RV32I.Word}
    (found : sail.regs.get? LeanRV32D.Register.nextPC = some value) :
    tick_pc () sail =
      .ok () (sailSetReg sail LeanRV32D.Register.PC value) := by
  have readNext : LeanRV32D.readReg LeanRV32D.Register.nextPC sail =
      .ok value sail := readReg_of_get found
  have writePc : LeanRV32D.writeReg LeanRV32D.Register.PC value sail =
      .ok () (sailSetReg sail LeanRV32D.Register.PC value) :=
    writeReg_eq_set sail (r := LeanRV32D.Register.PC) value
  have pcFound :
      (sailSetReg sail LeanRV32D.Register.PC value).regs.get?
          LeanRV32D.Register.PC = some value := by
    simp [sailSetReg, Std.ExtDHashMap.get?_insert]
  have readPc :
      LeanRV32D.readReg LeanRV32D.Register.PC
          (sailSetReg sail LeanRV32D.Register.PC value) =
        .ok value (sailSetReg sail LeanRV32D.Register.PC value) :=
    readReg_of_get pcFound
  simp only [tick_pc, bind, EStateM.bind, readNext, writePc, readPc]
  simp [pc_write_callback]
  rfl

/-- The generated instruction-level action for ADDI, normalized to the three
architecturally relevant operations: read rs1, write rd, retire successfully. -/
def sailAddi (immediate : BitVec 12) (rs1 rd : LeanRV32D.regidx) :
    LeanRV32D.SailM LeanRV32D.ExecutionResult := do
  let value ← rX_bits rs1
  wX_bits rd (value + immediate.signExtend 32)
  pure (.Retire_Success ())

theorem execute_ITYPE_addi_eq_sailAddi
    (immediate : BitVec 12) (rs1 rd : LeanRV32D.regidx) :
    execute_ITYPE immediate rs1 rd .ADDI = sailAddi immediate rs1 rd := by
  simp [execute_ITYPE, sailAddi, sign_extend, Sail.BitVec.signExtend,
    RETIRE_SUCCESS]

/-- Generated ADDI targeting x0 performs the source read but no register
write, and still reports successful retirement. -/
theorem sailAddi_x0 (immediate : BitVec 12) (rs1 : LeanRV32D.regidx) :
    sailAddi immediate rs1 (sailRegister 0) = (do
      let _ ← rX_bits rs1
      pure (.Retire_Success ())) := by
  simp [sailAddi, sailRegister, wX_bits, wX, Sail.BitVec.toNatInt]

/-- Canonical RV32I ADDI encoding, stated only in bridge vocabulary so it can
be compared directly with Sail's generated bidirectional mapping. -/
def encodeAddi (immediate : BitVec 12) (rs1 rd : RV32I.Register) :
    RV32I.Word :=
  immediate ++ (BitVec.ofNat 5 rs1.val) ++ 0b000#3 ++
    (BitVec.ofNat 5 rd.val) ++ 0b0010011#7

/-- The ADDI branch of Sail's generated forward instruction mapping, factored
out to avoid normalizing the other hundreds of generated instruction cases in
every bridge build. -/
def generatedAddiEncoding (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) : RV32I.Word :=
  immediate ++ encdec_reg_forwards (sailRegister rs1) ++
    encdec_iop_forwards .ADDI ++
    encdec_reg_forwards (sailRegister rd) ++ 0b0010011#7

theorem generated_addi_encoding_eq_clean (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) :
    generatedAddiEncoding immediate rs1 rd = encodeAddi immediate rs1 rd := by
  rfl

theorem clean_decodes_encoded_addi (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) :
    RV32I.Decoder.decode (encodeAddi immediate rs1 rd) =
      some (.addi rd rs1 immediate) := by
  have hopcode :
      RV32I.Decoder.opcode (encodeAddi immediate rs1 rd) = 0b0010011#7 := by
    simp only [RV32I.Decoder.opcode, encodeAddi]
    bv_decide
  have hfunct3 :
      RV32I.Decoder.funct3 (encodeAddi immediate rs1 rd) = 0b000#3 := by
    simp only [RV32I.Decoder.funct3, encodeAddi]
    bv_decide
  have hrd : RV32I.Decoder.rd (encodeAddi immediate rs1 rd) = rd := by
    clear hopcode hfunct3
    have bits :
        (encodeAddi immediate rs1 rd).extractLsb' 7 5 =
          BitVec.ofNat 5 rd.val := by
      simp only [encodeAddi]
      bv_decide
    simp [RV32I.Decoder.rd, bits]
  have hrs1 : RV32I.Decoder.rs1 (encodeAddi immediate rs1 rd) = rs1 := by
    clear hopcode hfunct3 hrd
    have bits :
        (encodeAddi immediate rs1 rd).extractLsb' 15 5 =
          BitVec.ofNat 5 rs1.val := by
      simp only [encodeAddi]
      bv_decide
    simp [RV32I.Decoder.rs1, bits]
  have himmediate :
      RV32I.Decoder.iImmediate (encodeAddi immediate rs1 rd) = immediate := by
    simp only [RV32I.Decoder.iImmediate, encodeAddi]
    bv_decide
  simp [RV32I.Decoder.decode, hopcode, hfunct3, hrd, hrs1, himmediate]

/-- The pure arithmetic used by the clean model is exactly the arithmetic in
the normalized generated Sail ADDI action. -/
theorem addi_value_eq_sail (immediate : BitVec 12) (value : RV32I.Word) :
    RV32I.Instruction.addi immediate value =
      value + sign_extend immediate := by
  simp [RV32I.Instruction.addi, sign_extend, Sail.BitVec.signExtend]

/-- The clean model's ADDI result exposes both architectural conventions that
surround the generated instruction action: x0 suppression is delegated to
`writeRegister`, and successful sequential retirement advances PC by four. -/
theorem clean_execute_addi (state : RV32I.State) (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) :
    RV32I.execute (.addi rd rs1 immediate) state =
      .done (.retired
        { state.writeRegister rd
            (state.readRegister rs1 + immediate.signExtend 32) with
          pc := state.pc + 4 }) := by
  rfl

theorem clean_execute_addi_x0 (state : RV32I.State)
    (immediate : BitVec 12) (rs1 : RV32I.Register) :
    RV32I.execute (.addi 0 rs1 immediate) state =
      .done (.retired { state with pc := state.pc + 4 }) := by
  simp [clean_execute_addi]

/-- The exact sequential-PC fragment surrounding a 32-bit instruction in the
generated Sail `run_hart_active`: stage `PC + 4` in `nextPC`. The generated
instruction executor itself intentionally does not commit `PC`. -/
def stageSequentialPc : LeanRV32D.SailM Unit := do
  LeanRV32D.writeReg LeanRV32D.Register.nextPC
    (Sail.BitVec.addInt (← LeanRV32D.readReg LeanRV32D.Register.PC) 4)

theorem clean_nextPc_eq_sail_value (state : RV32I.State) :
    RV32I.nextPc state = Sail.BitVec.addInt state.pc 4 := by
  simp [RV32I.nextPc, Sail.BitVec.addInt]

/-- From a related pre-state, the generated sequential-PC fragment stages
exactly the clean successor PC. This is an equality of Sail state actions, not
a claim that `execute_ITYPE` itself changes `PC`. -/
theorem stageSequentialPc_of_corresponds {clean : RV32I.State}
    {sail : SailState} (corresponds : StateCorresponds clean sail) :
    stageSequentialPc sail =
      LeanRV32D.writeReg LeanRV32D.Register.nextPC
        (RV32I.nextPc clean) sail := by
  have readPc : LeanRV32D.readReg LeanRV32D.Register.PC sail =
      .ok clean.pc sail := by
    simp [LeanRV32D.readReg, PreSail.readReg, get, getThe,
      MonadStateOf.get, EStateM.get, bind, EStateM.bind, corresponds.pc]
    rfl
  simp only [stageSequentialPc, bind, EStateM.bind, readPc,
    clean_nextPc_eq_sail_value]

/-- The clean architectural post-state of a successfully retired ADDI. -/
def cleanAddiPost (state : RV32I.State) (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) : RV32I.State :=
  { state.writeRegister rd
      (state.readRegister rs1 + immediate.signExtend 32) with
    pc := RV32I.nextPc state }

/-- The generated post-state of the selected Sail fragment: stage `nextPC`,
perform the generated integer-register write, then commit `PC`. -/
def sailAddiPost (sail : SailState) (state : RV32I.State)
    (immediate : BitVec 12) (rs1 rd : RV32I.Register) : SailState :=
  let staged :=
    sailSetReg sail LeanRV32D.Register.nextPC (RV32I.nextPc state)
  let written := sailWriteX staged rd
    (state.readRegister rs1 + immediate.signExtend 32)
  sailSetReg written LeanRV32D.Register.PC (RV32I.nextPc state)

/-- The exact generated actions selected for decoded ADDI comparison. This is
the base-instruction fragment of `run_hart_active` followed by the active-hart
PC commitment from `try_step`; fetch, decode, interrupt dispatch, counters,
hooks, and trap handling are deliberately outside this action. -/
def sailDecodedAddiStep (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) : LeanRV32D.SailM LeanRV32D.ExecutionResult := do
  stageSequentialPc
  let result ← execute_ITYPE immediate (sailRegister rs1)
    (sailRegister rd) .ADDI
  tick_pc ()
  pure result

theorem cleanAddiPost_pc (state : RV32I.State) (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) :
    (cleanAddiPost state immediate rs1 rd).pc = RV32I.nextPc state := by
  rfl

theorem cleanAddiPost_readRegister (state : RV32I.State)
    (immediate : BitVec 12) (rs1 rd r : RV32I.Register) :
    (cleanAddiPost state immediate rs1 rd).readRegister r =
      if rd.val = 0 then state.readRegister r
      else if r = rd then state.readRegister rs1 + immediate.signExtend 32
      else state.readRegister r := by
  exact clean_read_after_write state rd r
    (state.readRegister rs1 + immediate.signExtend 32)

theorem sailDecodedAddiStep_of_corresponds {state : RV32I.State}
    {sail : SailState} (corresponds : StateCorresponds state sail)
    (immediate : BitVec 12) (rs1 rd : RV32I.Register) :
    sailDecodedAddiStep immediate rs1 rd sail =
      .ok (.Retire_Success ())
        (sailAddiPost sail state immediate rs1 rd) := by
  let staged :=
    sailSetReg sail LeanRV32D.Register.nextPC (RV32I.nextPc state)
  let value := state.readRegister rs1 + immediate.signExtend 32
  have stageEq : stageSequentialPc sail = .ok () staged := by
    rw [stageSequentialPc_of_corresponds corresponds]
    exact writeReg_eq_set sail (r := LeanRV32D.Register.nextPC)
      (RV32I.nextPc state)
  have stagedRelation := corresponds.stageNextPc
  have stagedCorresponds : StateCorresponds state staged :=
    { pc := stagedRelation.pc
      register := stagedRelation.register }
  have readSource := rX_bits_of_corresponds stagedCorresponds rs1
  have writeDestination := wX_bits_sailRegister staged rd value
  have writeDestination' :
      wX_bits (sailRegister rd)
          (state.readRegister rs1 + immediate.signExtend 32) staged =
        .ok () (sailWriteX staged rd value) := by
    simpa [value] using writeDestination
  have executeEq :
      execute_ITYPE immediate (sailRegister rs1) (sailRegister rd) .ADDI
          staged =
        .ok (.Retire_Success ()) (sailWriteX staged rd value) := by
    rw [execute_ITYPE_addi_eq_sailAddi]
    simp only [sailAddi, bind, EStateM.bind, readSource, writeDestination']
    rfl
  have nextPcFound :
      (sailWriteX staged rd value).regs.get?
          LeanRV32D.Register.nextPC = some (RV32I.nextPc state) := by
    rw [sailWriteX_nextPc]
    simp [staged, sailSetReg, Std.ExtDHashMap.get?_insert]
  have tickEq := tick_pc_of_nextPc nextPcFound
  simp only [sailDecodedAddiStep, bind, EStateM.bind, stageEq, executeEq,
    tickEq]
  rfl

theorem sailAddiPost_corresponds {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) :
    StateCorresponds (cleanAddiPost state immediate rs1 rd)
      (sailAddiPost sail state immediate rs1 rd) := by
  let staged :=
    sailSetReg sail LeanRV32D.Register.nextPC (RV32I.nextPc state)
  let value := state.readRegister rs1 + immediate.signExtend 32
  have stagedRelation := corresponds.stageNextPc
  have stagedCorresponds : StateCorresponds state staged :=
    { pc := stagedRelation.pc
      register := stagedRelation.register }
  have writtenCorresponds := stagedCorresponds.writeX rd value
  have committedCorresponds := writtenCorresponds.setPc (RV32I.nextPc state)
  simpa [cleanAddiPost, sailAddiPost, staged, value] using
    committedCorresponds

theorem sailAddiPost_readRegister {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (immediate : BitVec 12)
    (rs1 rd r : RV32I.Register) :
    sailReadX (sailAddiPost sail state immediate rs1 rd) r =
      some (if rd.val = 0 then state.readRegister r
        else if r = rd then
          state.readRegister rs1 + immediate.signExtend 32
        else state.readRegister r) := by
  rw [(sailAddiPost_corresponds corresponds immediate rs1 rd).register r,
    cleanAddiPost_readRegister]

theorem sailAddiPost_destination {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) (rdNonzero : rd.val ≠ 0) :
    sailReadX (sailAddiPost sail state immediate rs1 rd) rd =
      some (state.readRegister rs1 + immediate.signExtend 32) := by
  simp [sailAddiPost_readRegister corresponds immediate rs1 rd rd,
    rdNonzero]

theorem sailAddiPost_unaffected {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (immediate : BitVec 12)
    (rs1 rd r : RV32I.Register) (different : r ≠ rd) :
    sailReadX (sailAddiPost sail state immediate rs1 rd) r =
      sailReadX sail r := by
  rw [sailAddiPost_readRegister corresponds immediate rs1 rd r,
    corresponds.register r]
  simp [different]

theorem sailAddiPost_x0 {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) :
    sailReadX (sailAddiPost sail state immediate rs1 rd) 0 = some 0 := by
  exact (sailAddiPost_corresponds corresponds immediate rs1 rd).register 0

theorem sailAddiPost_pc {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) :
    (sailAddiPost sail state immediate rs1 rd).regs.get?
        LeanRV32D.Register.PC = some (RV32I.nextPc state) := by
  exact (sailAddiPost_corresponds corresponds immediate rs1 rd).pc

/-- State-level simulation for decoded RV32I ADDI. A corresponding generated
pre-state runs the selected Sail stage/execute/commit fragment to successful
retirement, and its complete architectural projection corresponds to the
clean retired post-state. -/
theorem decoded_addi_state_simulation {state : RV32I.State}
    {sail : SailState} (corresponds : StateCorresponds state sail)
    (immediate : BitVec 12) (rs1 rd : RV32I.Register) :
    RV32I.execute (.addi rd rs1 immediate) state =
        .done (.retired (cleanAddiPost state immediate rs1 rd)) ∧
      sailDecodedAddiStep immediate rs1 rd sail =
        .ok (.Retire_Success ())
          (sailAddiPost sail state immediate rs1 rd) ∧
      StateCorresponds (cleanAddiPost state immediate rs1 rd)
        (sailAddiPost sail state immediate rs1 rd) := by
  constructor
  · rfl
  constructor
  · exact sailDecodedAddiStep_of_corresponds corresponds immediate rs1 rd
  · exact sailAddiPost_corresponds corresponds immediate rs1 rd

/-- A compact certificate for the first decoded-instruction bridge. It keeps
the generated monad on the Sail side and the pure interaction on the clean
side while recording every shared architectural fact explicitly. -/
structure AddiCorrespondence (state : RV32I.State) (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) : Prop where
  encoding : generatedAddiEncoding immediate rs1 rd =
    encodeAddi immediate rs1 rd
  decoding : RV32I.Decoder.decode (encodeAddi immediate rs1 rd) =
    some (.addi rd rs1 immediate)
  value : RV32I.Instruction.addi immediate (state.readRegister rs1) =
    state.readRegister rs1 + sign_extend immediate
  cleanExecution : RV32I.execute (.addi rd rs1 immediate) state =
    .done (.retired
      { state.writeRegister rd
          (state.readRegister rs1 + immediate.signExtend 32) with
        pc := state.pc + 4 })
  sailExecution :
    execute_ITYPE immediate (sailRegister rs1) (sailRegister rd) .ADDI =
      sailAddi immediate (sailRegister rs1) (sailRegister rd)
  pcAdvance : RV32I.nextPc state = Sail.BitVec.addInt state.pc 4

theorem decoded_addi_correspondence (state : RV32I.State)
    (immediate : BitVec 12) (rs1 rd : RV32I.Register) :
    AddiCorrespondence state immediate rs1 rd where
  encoding := generated_addi_encoding_eq_clean immediate rs1 rd
  decoding := clean_decodes_encoded_addi immediate rs1 rd
  value := addi_value_eq_sail immediate (state.readRegister rs1)
  cleanExecution := clean_execute_addi state immediate rs1 rd
  sailExecution := execute_ITYPE_addi_eq_sailAddi immediate
    (sailRegister rs1) (sailRegister rd)
  pcAdvance := clean_nextPc_eq_sail_value state

/-! ## Decoded LUI and AUIPC -/

/-- Canonical encoding shared by the two RV32I U-type instructions. -/
def encodeUtype (immediate : BitVec 20) (rd : RV32I.Register)
    (opcode : BitVec 7) : RV32I.Word :=
  immediate ++ BitVec.ofNat 5 rd.val ++ opcode

def encodeLui (immediate : BitVec 20) (rd : RV32I.Register) : RV32I.Word :=
  encodeUtype immediate rd 0b0110111#7

def encodeAuipc (immediate : BitVec 20) (rd : RV32I.Register) : RV32I.Word :=
  encodeUtype immediate rd 0b0010111#7

/-- The literal U-type branch of generated Sail's forward mapping, factored
without claiming equality to the monolithic generated encoder. -/
def generatedUtypeEncoding (immediate : BitVec 20) (rd : RV32I.Register)
    (op : LeanRV32D.uop) : RV32I.Word :=
  immediate ++ encdec_reg_forwards (sailRegister rd) ++
    encdec_uop_forwards op

theorem generated_lui_encoding_eq_clean (immediate : BitVec 20)
    (rd : RV32I.Register) :
    generatedUtypeEncoding immediate rd .LUI = encodeLui immediate rd := by
  rfl

theorem generated_auipc_encoding_eq_clean (immediate : BitVec 20)
    (rd : RV32I.Register) :
    generatedUtypeEncoding immediate rd .AUIPC = encodeAuipc immediate rd := by
  rfl

theorem clean_decodes_encoded_lui (immediate : BitVec 20)
    (rd : RV32I.Register) :
    RV32I.Decoder.decode (encodeLui immediate rd) =
      some (.lui rd immediate) := by
  have hopcode : RV32I.Decoder.opcode (encodeLui immediate rd) =
      0b0110111#7 := by
    simp only [RV32I.Decoder.opcode, encodeLui, encodeUtype]
    bv_decide
  have hrd : RV32I.Decoder.rd (encodeLui immediate rd) = rd := by
    have bits : (encodeLui immediate rd).extractLsb' 7 5 =
        BitVec.ofNat 5 rd.val := by
      simp only [encodeLui, encodeUtype]
      bv_decide
    simp [RV32I.Decoder.rd, bits]
  have himmediate :
      RV32I.Decoder.uImmediate (encodeLui immediate rd) = immediate := by
    simp only [RV32I.Decoder.uImmediate, encodeLui, encodeUtype]
    bv_decide
  simp [RV32I.Decoder.decode, hopcode, hrd, himmediate]

theorem clean_decodes_encoded_auipc (immediate : BitVec 20)
    (rd : RV32I.Register) :
    RV32I.Decoder.decode (encodeAuipc immediate rd) =
      some (.auipc rd immediate) := by
  have hopcode : RV32I.Decoder.opcode (encodeAuipc immediate rd) =
      0b0010111#7 := by
    simp only [RV32I.Decoder.opcode, encodeAuipc, encodeUtype]
    bv_decide
  have hrd : RV32I.Decoder.rd (encodeAuipc immediate rd) = rd := by
    have bits : (encodeAuipc immediate rd).extractLsb' 7 5 =
        BitVec.ofNat 5 rd.val := by
      simp only [encodeAuipc, encodeUtype]
      bv_decide
    simp [RV32I.Decoder.rd, bits]
  have himmediate :
      RV32I.Decoder.uImmediate (encodeAuipc immediate rd) = immediate := by
    simp only [RV32I.Decoder.uImmediate, encodeAuipc, encodeUtype]
    bv_decide
  simp [RV32I.Decoder.decode, hopcode, hrd, himmediate]

/-- Bridge-only selection of the clean result for generated U-type operations. -/
def cleanUtypeValue (state : RV32I.State) (immediate : BitVec 20) :
    LeanRV32D.uop → RV32I.Word
  | .LUI => RV32I.Instruction.lui immediate
  | .AUIPC => RV32I.Instruction.auipc immediate state.pc

theorem generated_utype_offset_eq_clean (immediate : BitVec 20) :
    sign_extend (immediate ++ 0x000#12) =
      RV32I.Instruction.upperImmediate immediate := by
  simp [sign_extend, Sail.BitVec.signExtend,
    RV32I.Instruction.upperImmediate]

theorem get_arch_pc_of_corresponds {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) :
    get_arch_pc () sail = .ok state.pc sail := by
  exact readReg_of_get corresponds.pc

theorem execute_UTYPE_of_corresponds {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (immediate : BitVec 20)
    (rd : RV32I.Register) (op : LeanRV32D.uop) :
    execute_UTYPE immediate (sailRegister rd) op sail =
      .ok (.Retire_Success ())
        (sailWriteX sail rd (cleanUtypeValue state immediate op)) := by
  have writeLui := wX_bits_sailRegister sail rd
    (RV32I.Instruction.lui immediate)
  have readPc := get_arch_pc_of_corresponds corresponds
  have writeAuipc := wX_bits_sailRegister sail rd
    (RV32I.Instruction.auipc immediate state.pc)
  cases op with
  | LUI =>
      rw [execute_UTYPE]
      simp only [generated_utype_offset_eq_clean]
      change (do
        wX_bits (sailRegister rd) (RV32I.Instruction.lui immediate)
        pure RETIRE_SUCCESS) sail = _
      simp only [bind, EStateM.bind, writeLui]
      rfl
  | AUIPC =>
      rw [execute_UTYPE]
      simp only [generated_utype_offset_eq_clean]
      change (do
        let pc ← get_arch_pc ()
        wX_bits (sailRegister rd) (RV32I.Instruction.auipc immediate pc)
        pure RETIRE_SUCCESS) sail = _
      simp only [bind, EStateM.bind, readPc, writeAuipc]
      rfl

/-- Shared staged/execute/commit fragment for decoded U-type instructions. -/
def sailDecodedUtypeStep (immediate : BitVec 20) (rd : RV32I.Register)
    (op : LeanRV32D.uop) : LeanRV32D.SailM LeanRV32D.ExecutionResult := do
  stageSequentialPc
  let result ← execute_UTYPE immediate (sailRegister rd) op
  tick_pc ()
  pure result

def cleanUtypePost (state : RV32I.State) (immediate : BitVec 20)
    (rd : RV32I.Register) (op : LeanRV32D.uop) : RV32I.State :=
  { state.writeRegister rd (cleanUtypeValue state immediate op) with
    pc := RV32I.nextPc state }

def sailUtypePost (sail : SailState) (state : RV32I.State)
    (immediate : BitVec 20) (rd : RV32I.Register)
    (op : LeanRV32D.uop) : SailState :=
  let staged :=
    sailSetReg sail LeanRV32D.Register.nextPC (RV32I.nextPc state)
  let written := sailWriteX staged rd (cleanUtypeValue state immediate op)
  sailSetReg written LeanRV32D.Register.PC (RV32I.nextPc state)

abbrev cleanLuiPost (state : RV32I.State) (immediate : BitVec 20)
    (rd : RV32I.Register) := cleanUtypePost state immediate rd .LUI

abbrev cleanAuipcPost (state : RV32I.State) (immediate : BitVec 20)
    (rd : RV32I.Register) := cleanUtypePost state immediate rd .AUIPC

abbrev sailLuiPost (sail : SailState) (state : RV32I.State)
    (immediate : BitVec 20) (rd : RV32I.Register) :=
  sailUtypePost sail state immediate rd .LUI

abbrev sailAuipcPost (sail : SailState) (state : RV32I.State)
    (immediate : BitVec 20) (rd : RV32I.Register) :=
  sailUtypePost sail state immediate rd .AUIPC

abbrev sailDecodedLuiStep (immediate : BitVec 20) (rd : RV32I.Register) :=
  sailDecodedUtypeStep immediate rd .LUI

abbrev sailDecodedAuipcStep (immediate : BitVec 20) (rd : RV32I.Register) :=
  sailDecodedUtypeStep immediate rd .AUIPC

theorem clean_execute_lui (state : RV32I.State) (immediate : BitVec 20)
    (rd : RV32I.Register) :
    RV32I.execute (.lui rd immediate) state =
      .done (.retired (cleanLuiPost state immediate rd)) := by
  rfl

theorem clean_execute_auipc (state : RV32I.State) (immediate : BitVec 20)
    (rd : RV32I.Register) :
    RV32I.execute (.auipc rd immediate) state =
      .done (.retired (cleanAuipcPost state immediate rd)) := by
  rfl

theorem sailDecodedUtypeStep_of_corresponds {state : RV32I.State}
    {sail : SailState} (corresponds : StateCorresponds state sail)
    (immediate : BitVec 20) (rd : RV32I.Register) (op : LeanRV32D.uop) :
    sailDecodedUtypeStep immediate rd op sail =
      .ok (.Retire_Success ()) (sailUtypePost sail state immediate rd op) := by
  let staged :=
    sailSetReg sail LeanRV32D.Register.nextPC (RV32I.nextPc state)
  let value := cleanUtypeValue state immediate op
  have stageEq : stageSequentialPc sail = .ok () staged := by
    rw [stageSequentialPc_of_corresponds corresponds]
    exact writeReg_eq_set sail (r := LeanRV32D.Register.nextPC)
      (RV32I.nextPc state)
  have stagedRelation := corresponds.stageNextPc
  have stagedCorresponds : StateCorresponds state staged :=
    { pc := stagedRelation.pc
      register := stagedRelation.register }
  have executeEq :
      execute_UTYPE immediate (sailRegister rd) op staged =
        .ok (.Retire_Success ()) (sailWriteX staged rd value) := by
    simpa [value] using
      execute_UTYPE_of_corresponds stagedCorresponds immediate rd op
  have nextPcFound :
      (sailWriteX staged rd value).regs.get?
          LeanRV32D.Register.nextPC = some (RV32I.nextPc state) := by
    rw [sailWriteX_nextPc]
    simp [staged, sailSetReg, Std.ExtDHashMap.get?_insert]
  have tickEq := tick_pc_of_nextPc nextPcFound
  simp only [sailDecodedUtypeStep, bind, EStateM.bind, stageEq, executeEq,
    tickEq]
  rfl

theorem sailUtypePost_corresponds {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (immediate : BitVec 20)
    (rd : RV32I.Register) (op : LeanRV32D.uop) :
    StateCorresponds (cleanUtypePost state immediate rd op)
      (sailUtypePost sail state immediate rd op) := by
  let staged :=
    sailSetReg sail LeanRV32D.Register.nextPC (RV32I.nextPc state)
  let value := cleanUtypeValue state immediate op
  have stagedRelation := corresponds.stageNextPc
  have stagedCorresponds : StateCorresponds state staged :=
    { pc := stagedRelation.pc
      register := stagedRelation.register }
  have writtenCorresponds := stagedCorresponds.writeX rd value
  have committedCorresponds := writtenCorresponds.setPc (RV32I.nextPc state)
  simpa [cleanUtypePost, sailUtypePost, staged, value] using
    committedCorresponds

theorem cleanUtypePost_readRegister (state : RV32I.State)
    (immediate : BitVec 20) (rd r : RV32I.Register)
    (op : LeanRV32D.uop) :
    (cleanUtypePost state immediate rd op).readRegister r =
      if rd.val = 0 then state.readRegister r
      else if r = rd then cleanUtypeValue state immediate op
      else state.readRegister r := by
  exact clean_read_after_write state rd r (cleanUtypeValue state immediate op)

theorem sailUtypePost_readRegister {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (immediate : BitVec 20)
    (rd r : RV32I.Register) (op : LeanRV32D.uop) :
    sailReadX (sailUtypePost sail state immediate rd op) r =
      some (if rd.val = 0 then state.readRegister r
        else if r = rd then cleanUtypeValue state immediate op
        else state.readRegister r) := by
  rw [(sailUtypePost_corresponds corresponds immediate rd op).register r,
    cleanUtypePost_readRegister]

theorem sailUtypePost_destination {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (immediate : BitVec 20)
    (rd : RV32I.Register) (op : LeanRV32D.uop) (rdNonzero : rd.val ≠ 0) :
    sailReadX (sailUtypePost sail state immediate rd op) rd =
      some (cleanUtypeValue state immediate op) := by
  simp [sailUtypePost_readRegister corresponds immediate rd rd op, rdNonzero]

theorem sailUtypePost_unaffected {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (immediate : BitVec 20)
    (rd r : RV32I.Register) (op : LeanRV32D.uop) (different : r ≠ rd) :
    sailReadX (sailUtypePost sail state immediate rd op) r = sailReadX sail r := by
  rw [sailUtypePost_readRegister corresponds immediate rd r op,
    corresponds.register r]
  simp [different]

theorem sailUtypePost_x0 {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (immediate : BitVec 20)
    (rd : RV32I.Register) (op : LeanRV32D.uop) :
    sailReadX (sailUtypePost sail state immediate rd op) 0 = some 0 := by
  exact (sailUtypePost_corresponds corresponds immediate rd op).register 0

theorem sailUtypePost_pc {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (immediate : BitVec 20)
    (rd : RV32I.Register) (op : LeanRV32D.uop) :
    (sailUtypePost sail state immediate rd op).regs.get?
        LeanRV32D.Register.PC = some (state.pc + 4) := by
  simpa [cleanUtypePost, RV32I.nextPc] using
    (sailUtypePost_corresponds corresponds immediate rd op).pc

theorem execute_UTYPE_lui_of_corresponds {state : RV32I.State}
    {sail : SailState} (corresponds : StateCorresponds state sail)
    (immediate : BitVec 20) (rd : RV32I.Register) :
    execute_UTYPE immediate (sailRegister rd) .LUI sail =
      .ok (.Retire_Success ())
        (sailWriteX sail rd (RV32I.Instruction.lui immediate)) := by
  exact execute_UTYPE_of_corresponds corresponds immediate rd .LUI

theorem execute_UTYPE_auipc_of_corresponds {state : RV32I.State}
    {sail : SailState} (corresponds : StateCorresponds state sail)
    (immediate : BitVec 20) (rd : RV32I.Register) :
    execute_UTYPE immediate (sailRegister rd) .AUIPC sail =
      .ok (.Retire_Success ())
        (sailWriteX sail rd (RV32I.Instruction.auipc immediate state.pc)) := by
  exact execute_UTYPE_of_corresponds corresponds immediate rd .AUIPC

/-- Reviewable decoded LUI certificate over the actual generated U-type
executor and the shared sequential stage/commit fragment. -/
structure DecodedLuiSimulation (state : RV32I.State) (sail : SailState)
    (immediate : BitVec 20) (rd : RV32I.Register) : Prop where
  encoding : generatedUtypeEncoding immediate rd .LUI = encodeLui immediate rd
  decoding : RV32I.Decoder.decode (encodeLui immediate rd) =
    some (.lui rd immediate)
  value : RV32I.Instruction.lui immediate = immediate ++ 0#12
  cleanExecution : RV32I.execute (.lui rd immediate) state =
    .done (.retired (cleanLuiPost state immediate rd))
  sailExecution : sailDecodedLuiStep immediate rd sail =
    .ok (.Retire_Success ()) (sailLuiPost sail state immediate rd)
  postCorrespondence : StateCorresponds (cleanLuiPost state immediate rd)
    (sailLuiPost sail state immediate rd)
  destination : rd.val ≠ 0 →
    sailReadX (sailLuiPost sail state immediate rd) rd =
      some (RV32I.Instruction.lui immediate)
  unaffected : ∀ r : RV32I.Register, r ≠ rd →
    sailReadX (sailLuiPost sail state immediate rd) r = sailReadX sail r
  x0 : sailReadX (sailLuiPost sail state immediate rd) 0 = some 0
  pc : (sailLuiPost sail state immediate rd).regs.get?
    LeanRV32D.Register.PC = some (state.pc + 4)

/-- State-level decoded LUI simulation. It assumes only initial architectural
state correspondence and introduces no memory or platform-path premise. -/
theorem decoded_lui_state_simulation {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (immediate : BitVec 20)
    (rd : RV32I.Register) :
    DecodedLuiSimulation state sail immediate rd where
  encoding := generated_lui_encoding_eq_clean immediate rd
  decoding := clean_decodes_encoded_lui immediate rd
  value := rfl
  cleanExecution := clean_execute_lui state immediate rd
  sailExecution := sailDecodedUtypeStep_of_corresponds corresponds
    immediate rd .LUI
  postCorrespondence := sailUtypePost_corresponds corresponds
    immediate rd .LUI
  destination := sailUtypePost_destination corresponds immediate rd .LUI
  unaffected := fun r =>
    sailUtypePost_unaffected corresponds immediate rd r .LUI
  x0 := sailUtypePost_x0 corresponds immediate rd .LUI
  pc := sailUtypePost_pc corresponds immediate rd .LUI

/-- Reviewable decoded AUIPC certificate. Its destination uses the old
architectural PC, while the shared outer fragment independently stages and
later commits `PC + 4`. -/
structure DecodedAuipcSimulation (state : RV32I.State) (sail : SailState)
    (immediate : BitVec 20) (rd : RV32I.Register) : Prop where
  encoding : generatedUtypeEncoding immediate rd .AUIPC =
    encodeAuipc immediate rd
  decoding : RV32I.Decoder.decode (encodeAuipc immediate rd) =
    some (.auipc rd immediate)
  value : RV32I.Instruction.auipc immediate state.pc =
    state.pc + (immediate ++ 0#12)
  cleanExecution : RV32I.execute (.auipc rd immediate) state =
    .done (.retired (cleanAuipcPost state immediate rd))
  sailExecution : sailDecodedAuipcStep immediate rd sail =
    .ok (.Retire_Success ()) (sailAuipcPost sail state immediate rd)
  postCorrespondence : StateCorresponds (cleanAuipcPost state immediate rd)
    (sailAuipcPost sail state immediate rd)
  destination : rd.val ≠ 0 →
    sailReadX (sailAuipcPost sail state immediate rd) rd =
      some (RV32I.Instruction.auipc immediate state.pc)
  unaffected : ∀ r : RV32I.Register, r ≠ rd →
    sailReadX (sailAuipcPost sail state immediate rd) r = sailReadX sail r
  x0 : sailReadX (sailAuipcPost sail state immediate rd) 0 = some 0
  pc : (sailAuipcPost sail state immediate rd).regs.get?
    LeanRV32D.Register.PC = some (state.pc + 4)

/-- State-level decoded AUIPC simulation with no memory or exception premise. -/
theorem decoded_auipc_state_simulation {state : RV32I.State}
    {sail : SailState} (corresponds : StateCorresponds state sail)
    (immediate : BitVec 20) (rd : RV32I.Register) :
    DecodedAuipcSimulation state sail immediate rd where
  encoding := generated_auipc_encoding_eq_clean immediate rd
  decoding := clean_decodes_encoded_auipc immediate rd
  value := rfl
  cleanExecution := clean_execute_auipc state immediate rd
  sailExecution := sailDecodedUtypeStep_of_corresponds corresponds
    immediate rd .AUIPC
  postCorrespondence := sailUtypePost_corresponds corresponds
    immediate rd .AUIPC
  destination := sailUtypePost_destination corresponds immediate rd .AUIPC
  unaffected := fun r =>
    sailUtypePost_unaffected corresponds immediate rd r .AUIPC
  x0 := sailUtypePost_x0 corresponds immediate rd .AUIPC
  pc := sailUtypePost_pc corresponds immediate rd .AUIPC

/-! ## Remaining register-only integer computations -/

/-- Clean post-state shared by every instruction that computes one word,
writes one integer destination, and advances sequentially. -/
def cleanComputePost (state : RV32I.State) (rd : RV32I.Register)
    (value : RV32I.Word) : RV32I.State :=
  { state.writeRegister rd value with pc := RV32I.nextPc state }

/-- Generated post-state for the corresponding stage/write/commit fragment. -/
def sailComputePost (sail : SailState) (state : RV32I.State)
    (rd : RV32I.Register) (value : RV32I.Word) : SailState :=
  let staged := sailSetReg sail LeanRV32D.Register.nextPC (RV32I.nextPc state)
  let written := sailWriteX staged rd value
  sailSetReg written LeanRV32D.Register.PC (RV32I.nextPc state)

/-- Surround an actual generated decoded-instruction executor with the same
sequential PC staging and commitment used by the generated step. -/
def sailDecodedComputeStep
    (action : LeanRV32D.SailM LeanRV32D.ExecutionResult) :
    LeanRV32D.SailM LeanRV32D.ExecutionResult := do
  stageSequentialPc
  let result ← action
  tick_pc ()
  pure result

theorem sailComputePost_corresponds {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (rd : RV32I.Register)
    (value : RV32I.Word) :
    StateCorresponds (cleanComputePost state rd value)
      (sailComputePost sail state rd value) := by
  let staged := sailSetReg sail LeanRV32D.Register.nextPC (RV32I.nextPc state)
  have stagedRelation := corresponds.stageNextPc
  have stagedCorresponds : StateCorresponds state staged :=
    { pc := stagedRelation.pc, register := stagedRelation.register }
  have writtenCorresponds := stagedCorresponds.writeX rd value
  have committedCorresponds := writtenCorresponds.setPc (RV32I.nextPc state)
  simpa [cleanComputePost, sailComputePost, staged] using committedCorresponds

theorem cleanComputePost_readRegister (state : RV32I.State)
    (rd r : RV32I.Register) (value : RV32I.Word) :
    (cleanComputePost state rd value).readRegister r =
      if rd.val = 0 then state.readRegister r
      else if r = rd then value else state.readRegister r := by
  exact clean_read_after_write state rd r value

theorem sailComputePost_destination {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (rd : RV32I.Register)
    (value : RV32I.Word) (rdNonzero : rd.val ≠ 0) :
    sailReadX (sailComputePost sail state rd value) rd = some value := by
  rw [(sailComputePost_corresponds corresponds rd value).register rd,
    cleanComputePost_readRegister]
  simp [rdNonzero]

theorem sailComputePost_unaffected {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (rd r : RV32I.Register)
    (value : RV32I.Word) (different : r ≠ rd) :
    sailReadX (sailComputePost sail state rd value) r = sailReadX sail r := by
  rw [(sailComputePost_corresponds corresponds rd value).register r,
    cleanComputePost_readRegister, corresponds.register r]
  simp [different]

theorem sailComputePost_x0 {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (rd : RV32I.Register)
    (value : RV32I.Word) :
    sailReadX (sailComputePost sail state rd value) 0 = some 0 :=
  (sailComputePost_corresponds corresponds rd value).register 0

theorem sailComputePost_pc {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (rd : RV32I.Register)
    (value : RV32I.Word) :
    (sailComputePost sail state rd value).regs.get? LeanRV32D.Register.PC =
      some (state.pc + 4) := by
  simpa [cleanComputePost, RV32I.nextPc] using
    (sailComputePost_corresponds corresponds rd value).pc

/-- Generic state proof for an actual generated executor that writes the
specified value and retires successfully. -/
theorem sailDecodedComputeStep_of_action {state : RV32I.State}
    {sail : SailState} (corresponds : StateCorresponds state sail)
    (rd : RV32I.Register) (value : RV32I.Word)
    (action : LeanRV32D.SailM LeanRV32D.ExecutionResult)
    (runs : let staged :=
        sailSetReg sail LeanRV32D.Register.nextPC (RV32I.nextPc state)
      action staged = .ok (.Retire_Success ()) (sailWriteX staged rd value)) :
    sailDecodedComputeStep action sail =
      .ok (.Retire_Success ()) (sailComputePost sail state rd value) := by
  let staged := sailSetReg sail LeanRV32D.Register.nextPC (RV32I.nextPc state)
  have stageEq : stageSequentialPc sail = .ok () staged := by
    rw [stageSequentialPc_of_corresponds corresponds]
    exact writeReg_eq_set sail (r := LeanRV32D.Register.nextPC)
      (RV32I.nextPc state)
  have nextPcFound :
      (sailWriteX staged rd value).regs.get? LeanRV32D.Register.nextPC =
        some (RV32I.nextPc state) := by
    rw [sailWriteX_nextPc]
    simp [staged, sailSetReg, Std.ExtDHashMap.get?_insert]
  have tickEq := tick_pc_of_nextPc nextPcFound
  change action staged =
    .ok (.Retire_Success ()) (sailWriteX staged rd value) at runs
  simp only [sailDecodedComputeStep, bind, EStateM.bind, stageEq, runs,
    tickEq]
  rfl

/-! ### I-type non-shift computations -/

def cleanItypeInstruction (op : LeanRV32D.iop) (rd rs1 : RV32I.Register)
    (immediate : BitVec 12) : RV32I.DecodedInstruction :=
  match op with
  | .ADDI => .addi rd rs1 immediate
  | .SLTI => .slti rd rs1 immediate
  | .SLTIU => .sltiu rd rs1 immediate
  | .XORI => .xori rd rs1 immediate
  | .ORI => .ori rd rs1 immediate
  | .ANDI => .andi rd rs1 immediate

def cleanItypeValue (op : LeanRV32D.iop) (immediate : BitVec 12)
    (rs1Value : RV32I.Word) : RV32I.Word :=
  match op with
  | .ADDI => RV32I.Instruction.addi immediate rs1Value
  | .SLTI => RV32I.Instruction.slti immediate rs1Value
  | .SLTIU => RV32I.Instruction.sltiu immediate rs1Value
  | .XORI => RV32I.Instruction.xori immediate rs1Value
  | .ORI => RV32I.Instruction.ori immediate rs1Value
  | .ANDI => RV32I.Instruction.andi immediate rs1Value

theorem clean_execute_itype (state : RV32I.State) (op : LeanRV32D.iop)
    (immediate : BitVec 12) (rs1 rd : RV32I.Register) :
    RV32I.execute (cleanItypeInstruction op rd rs1 immediate) state =
      .done (.retired (cleanComputePost state rd
        (cleanItypeValue op immediate (state.readRegister rs1)))) := by
  cases op <;> rfl

def sailItypeCompute (op : LeanRV32D.iop) (immediate : BitVec 12)
    (rs1 rd : LeanRV32D.regidx) : LeanRV32D.SailM LeanRV32D.ExecutionResult := do
  let source ← rX_bits rs1
  wX_bits rd (cleanItypeValue op immediate source)
  pure (.Retire_Success ())

theorem sail_zeroExtend_bool_to_bit (value : Bool) :
    (LeanRV32D.zero_extend (m := 32) (bool_to_bit value)) =
      (BitVec.ofBool value).zeroExtend 32 := by
  cases value <;> rfl

theorem execute_ITYPE_eq_sailItypeCompute (op : LeanRV32D.iop)
    (immediate : BitVec 12) (rs1 rd : LeanRV32D.regidx) :
    execute_ITYPE immediate rs1 rd op =
      sailItypeCompute op immediate rs1 rd := by
  cases op <;>
    simp [execute_ITYPE, sailItypeCompute, cleanItypeValue,
      RV32I.Instruction.addi, RV32I.Instruction.slti,
      RV32I.Instruction.sltiu, RV32I.Instruction.xori,
      RV32I.Instruction.ori, RV32I.Instruction.andi,
      sign_extend, Sail.BitVec.signExtend, sail_zeroExtend_bool_to_bit,
      zopz0zI_s, zopz0zI_u, BitVec.slt, BitVec.ult,
      Sail.BitVec.toNatInt, RETIRE_SUCCESS]
  all_goals rfl

theorem execute_ITYPE_compute_of_corresponds {state : RV32I.State}
    {sail : SailState} (corresponds : StateCorresponds state sail)
    (op : LeanRV32D.iop) (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) :
    execute_ITYPE immediate (sailRegister rs1) (sailRegister rd) op sail =
      .ok (.Retire_Success ())
        (sailWriteX sail rd
          (cleanItypeValue op immediate (state.readRegister rs1))) := by
  have readSource := rX_bits_of_corresponds corresponds rs1
  have writeDestination := wX_bits_sailRegister sail rd
    (cleanItypeValue op immediate (state.readRegister rs1))
  rw [execute_ITYPE_eq_sailItypeCompute]
  simp only [sailItypeCompute, bind, EStateM.bind, readSource,
    writeDestination]
  rfl

def sailDecodedItypeStep (op : LeanRV32D.iop) (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) : LeanRV32D.SailM LeanRV32D.ExecutionResult :=
  sailDecodedComputeStep
    (execute_ITYPE immediate (sailRegister rs1) (sailRegister rd) op)

/-- One theorem covers ADDI and every remaining non-shift OP-IMM operation,
while retaining the actual generated `execute_ITYPE` call. -/
structure DecodedItypeSimulation (state : RV32I.State) (sail : SailState)
    (op : LeanRV32D.iop) (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) : Prop where
  cleanExecution :
    RV32I.execute (cleanItypeInstruction op rd rs1 immediate) state =
      .done (.retired (cleanComputePost state rd
        (cleanItypeValue op immediate (state.readRegister rs1))))
  sailExecution : sailDecodedItypeStep op immediate rs1 rd sail =
    .ok (.Retire_Success ()) (sailComputePost sail state rd
      (cleanItypeValue op immediate (state.readRegister rs1)))
  postCorrespondence : StateCorresponds
    (cleanComputePost state rd
      (cleanItypeValue op immediate (state.readRegister rs1)))
    (sailComputePost sail state rd
      (cleanItypeValue op immediate (state.readRegister rs1)))
  destination : rd.val ≠ 0 →
    sailReadX (sailComputePost sail state rd
      (cleanItypeValue op immediate (state.readRegister rs1))) rd =
      some (cleanItypeValue op immediate (state.readRegister rs1))
  unaffected : ∀ r : RV32I.Register, r ≠ rd →
    sailReadX (sailComputePost sail state rd
      (cleanItypeValue op immediate (state.readRegister rs1))) r = sailReadX sail r
  x0 : sailReadX (sailComputePost sail state rd
    (cleanItypeValue op immediate (state.readRegister rs1))) 0 = some 0
  pc : (sailComputePost sail state rd
    (cleanItypeValue op immediate (state.readRegister rs1))).regs.get?
      LeanRV32D.Register.PC = some (state.pc + 4)

theorem decoded_itype_state_simulation {state : RV32I.State}
    {sail : SailState} (corresponds : StateCorresponds state sail)
    (op : LeanRV32D.iop) (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) :
    DecodedItypeSimulation state sail op immediate rs1 rd := by
  let value := cleanItypeValue op immediate (state.readRegister rs1)
  have actionRuns :
      let staged := sailSetReg sail LeanRV32D.Register.nextPC (RV32I.nextPc state)
      execute_ITYPE immediate (sailRegister rs1) (sailRegister rd) op staged =
        .ok (.Retire_Success ()) (sailWriteX staged rd value) := by
    exact execute_ITYPE_compute_of_corresponds
      { pc := corresponds.stageNextPc.pc,
        register := corresponds.stageNextPc.register }
      op immediate rs1 rd
  constructor
  · exact clean_execute_itype state op immediate rs1 rd
  · exact sailDecodedComputeStep_of_action corresponds rd value _ actionRuns
  · exact sailComputePost_corresponds corresponds rd value
  · exact sailComputePost_destination corresponds rd value
  · exact fun r => sailComputePost_unaffected corresponds rd r value
  · exact sailComputePost_x0 corresponds rd value
  · exact sailComputePost_pc corresponds rd value

/-! ### Shift-immediate computations -/

def cleanShiftInstruction (op : LeanRV32D.sop) (rd rs1 : RV32I.Register)
    (shamt : BitVec 5) : RV32I.DecodedInstruction :=
  match op with
  | .SLLI => .slli rd rs1 shamt
  | .SRLI => .srli rd rs1 shamt
  | .SRAI => .srai rd rs1 shamt

def cleanShiftValue (op : LeanRV32D.sop) (shamt : BitVec 5)
    (rs1Value : RV32I.Word) : RV32I.Word :=
  match op with
  | .SLLI => RV32I.Instruction.slli shamt rs1Value
  | .SRLI => RV32I.Instruction.srli shamt rs1Value
  | .SRAI => RV32I.Instruction.srai shamt rs1Value

def sailShiftAmount (shamt : BitVec 5) : BitVec 6 := 0#1 ++ shamt

theorem generated_log2_xlen_eq_five : LeanRV32D.Functions.log2_xlen = 5 := rfl

theorem generated_shift_amount_toNat_eq_clean (shamt : BitVec 5) :
    (Sail.BitVec.extractLsb (sailShiftAmount shamt)
        ((LeanRV32D.Functions.log2_xlen : Int) -i 1) 0).toNat = shamt.toNat := by
  change ((sailShiftAmount shamt).extractLsb' 0 5).toNat = shamt.toNat
  simp [sailShiftAmount]
  rw [BitVec.toNat_append]
  rw [show (0#1).toNat = 0 by rfl]
  simp only [Nat.zero_shiftLeft, Nat.zero_or]
  exact Nat.mod_eq_of_lt shamt.isLt

theorem clean_execute_shift (state : RV32I.State) (op : LeanRV32D.sop)
    (shamt : BitVec 5) (rs1 rd : RV32I.Register) :
    RV32I.execute (cleanShiftInstruction op rd rs1 shamt) state =
      .done (.retired (cleanComputePost state rd
        (cleanShiftValue op shamt (state.readRegister rs1)))) := by
  cases op <;> rfl

def sailShiftCompute (op : LeanRV32D.sop) (shamt : BitVec 5)
    (rs1 rd : LeanRV32D.regidx) : LeanRV32D.SailM LeanRV32D.ExecutionResult := do
  let source ← rX_bits rs1
  wX_bits rd (cleanShiftValue op shamt source)
  pure (.Retire_Success ())

theorem execute_SHIFTIOP_eq_sailShiftCompute (op : LeanRV32D.sop)
    (shamt : BitVec 5) (rs1 rd : LeanRV32D.regidx) :
    execute_SHIFTIOP (sailShiftAmount shamt) rs1 rd op =
      sailShiftCompute op shamt rs1 rd := by
  cases op <;>
    simp [execute_SHIFTIOP, sailShiftCompute, cleanShiftValue,
      RV32I.Instruction.slli, RV32I.Instruction.srli,
      RV32I.Instruction.srai,
      Sail.shift_bits_left, Sail.shift_bits_right,
      shift_bits_right_arith, Sail.BitVec.toNatInt, RETIRE_SUCCESS]
  all_goals rw [generated_shift_amount_toNat_eq_clean]

theorem execute_SHIFTIOP_compute_of_corresponds {state : RV32I.State}
    {sail : SailState} (corresponds : StateCorresponds state sail)
    (op : LeanRV32D.sop) (shamt : BitVec 5)
    (rs1 rd : RV32I.Register) :
    execute_SHIFTIOP (sailShiftAmount shamt) (sailRegister rs1)
        (sailRegister rd) op sail =
      .ok (.Retire_Success ()) (sailWriteX sail rd
        (cleanShiftValue op shamt (state.readRegister rs1))) := by
  have readSource := rX_bits_of_corresponds corresponds rs1
  have writeDestination := wX_bits_sailRegister sail rd
    (cleanShiftValue op shamt (state.readRegister rs1))
  rw [execute_SHIFTIOP_eq_sailShiftCompute]
  simp only [sailShiftCompute, bind, EStateM.bind, readSource,
    writeDestination]
  rfl

def sailDecodedShiftStep (op : LeanRV32D.sop) (shamt : BitVec 5)
    (rs1 rd : RV32I.Register) : LeanRV32D.SailM LeanRV32D.ExecutionResult :=
  sailDecodedComputeStep (execute_SHIFTIOP (sailShiftAmount shamt)
    (sailRegister rs1) (sailRegister rd) op)

structure DecodedShiftSimulation (state : RV32I.State) (sail : SailState)
    (op : LeanRV32D.sop) (shamt : BitVec 5)
    (rs1 rd : RV32I.Register) : Prop where
  cleanExecution :
    RV32I.execute (cleanShiftInstruction op rd rs1 shamt) state =
      .done (.retired (cleanComputePost state rd
        (cleanShiftValue op shamt (state.readRegister rs1))))
  sailExecution : sailDecodedShiftStep op shamt rs1 rd sail =
    .ok (.Retire_Success ()) (sailComputePost sail state rd
      (cleanShiftValue op shamt (state.readRegister rs1)))
  postCorrespondence : StateCorresponds
    (cleanComputePost state rd (cleanShiftValue op shamt (state.readRegister rs1)))
    (sailComputePost sail state rd (cleanShiftValue op shamt (state.readRegister rs1)))
  destination : rd.val ≠ 0 → sailReadX (sailComputePost sail state rd
    (cleanShiftValue op shamt (state.readRegister rs1))) rd =
      some (cleanShiftValue op shamt (state.readRegister rs1))
  unaffected : ∀ r : RV32I.Register, r ≠ rd →
    sailReadX (sailComputePost sail state rd
      (cleanShiftValue op shamt (state.readRegister rs1))) r = sailReadX sail r
  x0 : sailReadX (sailComputePost sail state rd
    (cleanShiftValue op shamt (state.readRegister rs1))) 0 = some 0
  pc : (sailComputePost sail state rd
    (cleanShiftValue op shamt (state.readRegister rs1))).regs.get?
      LeanRV32D.Register.PC = some (state.pc + 4)

theorem decoded_shift_state_simulation {state : RV32I.State}
    {sail : SailState} (corresponds : StateCorresponds state sail)
    (op : LeanRV32D.sop) (shamt : BitVec 5) (rs1 rd : RV32I.Register) :
    DecodedShiftSimulation state sail op shamt rs1 rd := by
  let value := cleanShiftValue op shamt (state.readRegister rs1)
  have actionRuns :
      let staged := sailSetReg sail LeanRV32D.Register.nextPC (RV32I.nextPc state)
      execute_SHIFTIOP (sailShiftAmount shamt) (sailRegister rs1)
          (sailRegister rd) op staged =
        .ok (.Retire_Success ()) (sailWriteX staged rd value) := by
    exact execute_SHIFTIOP_compute_of_corresponds
      { pc := corresponds.stageNextPc.pc,
        register := corresponds.stageNextPc.register }
      op shamt rs1 rd
  constructor
  · exact clean_execute_shift state op shamt rs1 rd
  · exact sailDecodedComputeStep_of_action corresponds rd value _ actionRuns
  · exact sailComputePost_corresponds corresponds rd value
  · exact sailComputePost_destination corresponds rd value
  · exact fun r => sailComputePost_unaffected corresponds rd r value
  · exact sailComputePost_x0 corresponds rd value
  · exact sailComputePost_pc corresponds rd value

/-! ### Register-register computations -/

def cleanRtypeInstruction (op : LeanRV32D.rop) (rd rs1 rs2 : RV32I.Register) :
    RV32I.DecodedInstruction :=
  match op with
  | .ADD => .add rd rs1 rs2
  | .SUB => .sub rd rs1 rs2
  | .SLL => .sll rd rs1 rs2
  | .SLT => .slt rd rs1 rs2
  | .SLTU => .sltu rd rs1 rs2
  | .XOR => .xor rd rs1 rs2
  | .SRL => .srl rd rs1 rs2
  | .SRA => .sra rd rs1 rs2
  | .OR => .or rd rs1 rs2
  | .AND => .and rd rs1 rs2

def cleanRtypeValue (op : LeanRV32D.rop) (rs2Value rs1Value : RV32I.Word) :
    RV32I.Word :=
  match op with
  | .ADD => RV32I.Instruction.add rs2Value rs1Value
  | .SUB => RV32I.Instruction.sub rs2Value rs1Value
  | .SLL => RV32I.Instruction.sll rs2Value rs1Value
  | .SLT => RV32I.Instruction.slt rs2Value rs1Value
  | .SLTU => RV32I.Instruction.sltu rs2Value rs1Value
  | .XOR => RV32I.Instruction.xor rs2Value rs1Value
  | .SRL => RV32I.Instruction.srl rs2Value rs1Value
  | .SRA => RV32I.Instruction.sra rs2Value rs1Value
  | .OR => RV32I.Instruction.or rs2Value rs1Value
  | .AND => RV32I.Instruction.and rs2Value rs1Value

theorem generated_register_shift_amount_eq_clean (value : RV32I.Word) :
    (Sail.BitVec.extractLsb value
      ((LeanRV32D.Functions.log2_xlen : Int) -i 1) 0).toNat =
        (value.extractLsb' 0 5).toNat := by
  rfl

theorem clean_execute_rtype (state : RV32I.State) (op : LeanRV32D.rop)
    (rs2 rs1 rd : RV32I.Register) :
    RV32I.execute (cleanRtypeInstruction op rd rs1 rs2) state =
      .done (.retired (cleanComputePost state rd
        (cleanRtypeValue op (state.readRegister rs2)
          (state.readRegister rs1)))) := by
  cases op <;> rfl

def sailRtypeCompute (op : LeanRV32D.rop)
    (rs2 rs1 rd : LeanRV32D.regidx) : LeanRV32D.SailM LeanRV32D.ExecutionResult := do
  let source1 ← rX_bits rs1
  let source2 ← rX_bits rs2
  wX_bits rd (cleanRtypeValue op source2 source1)
  pure (.Retire_Success ())

theorem execute_RTYPE_eq_sailRtypeCompute (op : LeanRV32D.rop)
    (rs2 rs1 rd : LeanRV32D.regidx) :
    execute_RTYPE rs2 rs1 rd op = sailRtypeCompute op rs2 rs1 rd := by
  cases op <;>
    simp [execute_RTYPE, sailRtypeCompute, cleanRtypeValue,
      RV32I.Instruction.add, RV32I.Instruction.sub, RV32I.Instruction.sll,
      RV32I.Instruction.slt, RV32I.Instruction.sltu, RV32I.Instruction.xor,
      RV32I.Instruction.srl, RV32I.Instruction.sra, RV32I.Instruction.or,
      RV32I.Instruction.and, Sail.shift_bits_left, Sail.shift_bits_right,
      shift_bits_right_arith, Sail.BitVec.toNatInt, sail_zeroExtend_bool_to_bit,
      zopz0zI_s, zopz0zI_u, BitVec.slt, BitVec.ult, RETIRE_SUCCESS]
  all_goals try rw [generated_register_shift_amount_eq_clean]
  all_goals rfl

theorem execute_RTYPE_compute_of_corresponds {state : RV32I.State}
    {sail : SailState} (corresponds : StateCorresponds state sail)
    (op : LeanRV32D.rop) (rs2 rs1 rd : RV32I.Register) :
    execute_RTYPE (sailRegister rs2) (sailRegister rs1) (sailRegister rd) op sail =
      .ok (.Retire_Success ()) (sailWriteX sail rd
        (cleanRtypeValue op (state.readRegister rs2) (state.readRegister rs1))) := by
  have readSource1 := rX_bits_of_corresponds corresponds rs1
  have readSource2 := rX_bits_of_corresponds corresponds rs2
  have writeDestination := wX_bits_sailRegister sail rd
    (cleanRtypeValue op (state.readRegister rs2) (state.readRegister rs1))
  rw [execute_RTYPE_eq_sailRtypeCompute]
  simp only [sailRtypeCompute, bind, EStateM.bind, readSource1, readSource2,
    writeDestination]
  rfl

def sailDecodedRtypeStep (op : LeanRV32D.rop)
    (rs2 rs1 rd : RV32I.Register) : LeanRV32D.SailM LeanRV32D.ExecutionResult :=
  sailDecodedComputeStep (execute_RTYPE (sailRegister rs2)
    (sailRegister rs1) (sailRegister rd) op)

structure DecodedRtypeSimulation (state : RV32I.State) (sail : SailState)
    (op : LeanRV32D.rop) (rs2 rs1 rd : RV32I.Register) : Prop where
  cleanExecution :
    RV32I.execute (cleanRtypeInstruction op rd rs1 rs2) state =
      .done (.retired (cleanComputePost state rd
        (cleanRtypeValue op (state.readRegister rs2) (state.readRegister rs1))))
  sailExecution : sailDecodedRtypeStep op rs2 rs1 rd sail =
    .ok (.Retire_Success ()) (sailComputePost sail state rd
      (cleanRtypeValue op (state.readRegister rs2) (state.readRegister rs1)))
  postCorrespondence : StateCorresponds
    (cleanComputePost state rd
      (cleanRtypeValue op (state.readRegister rs2) (state.readRegister rs1)))
    (sailComputePost sail state rd
      (cleanRtypeValue op (state.readRegister rs2) (state.readRegister rs1)))
  destination : rd.val ≠ 0 → sailReadX (sailComputePost sail state rd
    (cleanRtypeValue op (state.readRegister rs2) (state.readRegister rs1))) rd =
      some (cleanRtypeValue op (state.readRegister rs2) (state.readRegister rs1))
  unaffected : ∀ r : RV32I.Register, r ≠ rd →
    sailReadX (sailComputePost sail state rd
      (cleanRtypeValue op (state.readRegister rs2) (state.readRegister rs1))) r =
        sailReadX sail r
  x0 : sailReadX (sailComputePost sail state rd
    (cleanRtypeValue op (state.readRegister rs2) (state.readRegister rs1))) 0 = some 0
  pc : (sailComputePost sail state rd
    (cleanRtypeValue op (state.readRegister rs2) (state.readRegister rs1))).regs.get?
      LeanRV32D.Register.PC = some (state.pc + 4)

theorem decoded_rtype_state_simulation {state : RV32I.State}
    {sail : SailState} (corresponds : StateCorresponds state sail)
    (op : LeanRV32D.rop) (rs2 rs1 rd : RV32I.Register) :
    DecodedRtypeSimulation state sail op rs2 rs1 rd := by
  let value := cleanRtypeValue op (state.readRegister rs2) (state.readRegister rs1)
  have actionRuns :
      let staged := sailSetReg sail LeanRV32D.Register.nextPC (RV32I.nextPc state)
      execute_RTYPE (sailRegister rs2) (sailRegister rs1) (sailRegister rd) op staged =
        .ok (.Retire_Success ()) (sailWriteX staged rd value) := by
    exact execute_RTYPE_compute_of_corresponds
      { pc := corresponds.stageNextPc.pc,
        register := corresponds.stageNextPc.register }
      op rs2 rs1 rd
  constructor
  · exact clean_execute_rtype state op rs2 rs1 rd
  · exact sailDecodedComputeStep_of_action corresponds rd value _ actionRuns
  · exact sailComputePost_corresponds corresponds rd value
  · exact sailComputePost_destination corresponds rd value
  · exact fun r => sailComputePost_unaffected corresponds rd r value
  · exact sailComputePost_x0 corresponds rd value
  · exact sailComputePost_pc corresponds rd value

/-! Named entry points make the quantified family results directly usable at
each RV32I mnemonic. -/

theorem decoded_slti_state_simulation {state : RV32I.State} {sail : SailState}
    (h : StateCorresponds state sail) (imm : BitVec 12) (rs1 rd : RV32I.Register) :
    DecodedItypeSimulation state sail .SLTI imm rs1 rd :=
  decoded_itype_state_simulation h .SLTI imm rs1 rd

theorem decoded_sltiu_state_simulation {state : RV32I.State} {sail : SailState}
    (h : StateCorresponds state sail) (imm : BitVec 12) (rs1 rd : RV32I.Register) :
    DecodedItypeSimulation state sail .SLTIU imm rs1 rd :=
  decoded_itype_state_simulation h .SLTIU imm rs1 rd

theorem decoded_xori_state_simulation {state : RV32I.State} {sail : SailState}
    (h : StateCorresponds state sail) (imm : BitVec 12) (rs1 rd : RV32I.Register) :
    DecodedItypeSimulation state sail .XORI imm rs1 rd :=
  decoded_itype_state_simulation h .XORI imm rs1 rd

theorem decoded_ori_state_simulation {state : RV32I.State} {sail : SailState}
    (h : StateCorresponds state sail) (imm : BitVec 12) (rs1 rd : RV32I.Register) :
    DecodedItypeSimulation state sail .ORI imm rs1 rd :=
  decoded_itype_state_simulation h .ORI imm rs1 rd

theorem decoded_andi_state_simulation {state : RV32I.State} {sail : SailState}
    (h : StateCorresponds state sail) (imm : BitVec 12) (rs1 rd : RV32I.Register) :
    DecodedItypeSimulation state sail .ANDI imm rs1 rd :=
  decoded_itype_state_simulation h .ANDI imm rs1 rd

theorem decoded_slli_state_simulation {state : RV32I.State} {sail : SailState}
    (h : StateCorresponds state sail) (shamt : BitVec 5) (rs1 rd : RV32I.Register) :
    DecodedShiftSimulation state sail .SLLI shamt rs1 rd :=
  decoded_shift_state_simulation h .SLLI shamt rs1 rd

theorem decoded_srli_state_simulation {state : RV32I.State} {sail : SailState}
    (h : StateCorresponds state sail) (shamt : BitVec 5) (rs1 rd : RV32I.Register) :
    DecodedShiftSimulation state sail .SRLI shamt rs1 rd :=
  decoded_shift_state_simulation h .SRLI shamt rs1 rd

theorem decoded_srai_state_simulation {state : RV32I.State} {sail : SailState}
    (h : StateCorresponds state sail) (shamt : BitVec 5) (rs1 rd : RV32I.Register) :
    DecodedShiftSimulation state sail .SRAI shamt rs1 rd :=
  decoded_shift_state_simulation h .SRAI shamt rs1 rd

theorem decoded_add_state_simulation {state : RV32I.State} {sail : SailState}
    (h : StateCorresponds state sail) (rs2 rs1 rd : RV32I.Register) :
    DecodedRtypeSimulation state sail .ADD rs2 rs1 rd :=
  decoded_rtype_state_simulation h .ADD rs2 rs1 rd

theorem decoded_sub_state_simulation {state : RV32I.State} {sail : SailState}
    (h : StateCorresponds state sail) (rs2 rs1 rd : RV32I.Register) :
    DecodedRtypeSimulation state sail .SUB rs2 rs1 rd :=
  decoded_rtype_state_simulation h .SUB rs2 rs1 rd

theorem decoded_sll_state_simulation {state : RV32I.State} {sail : SailState}
    (h : StateCorresponds state sail) (rs2 rs1 rd : RV32I.Register) :
    DecodedRtypeSimulation state sail .SLL rs2 rs1 rd :=
  decoded_rtype_state_simulation h .SLL rs2 rs1 rd

theorem decoded_slt_state_simulation {state : RV32I.State} {sail : SailState}
    (h : StateCorresponds state sail) (rs2 rs1 rd : RV32I.Register) :
    DecodedRtypeSimulation state sail .SLT rs2 rs1 rd :=
  decoded_rtype_state_simulation h .SLT rs2 rs1 rd

theorem decoded_sltu_state_simulation {state : RV32I.State} {sail : SailState}
    (h : StateCorresponds state sail) (rs2 rs1 rd : RV32I.Register) :
    DecodedRtypeSimulation state sail .SLTU rs2 rs1 rd :=
  decoded_rtype_state_simulation h .SLTU rs2 rs1 rd

theorem decoded_xor_state_simulation {state : RV32I.State} {sail : SailState}
    (h : StateCorresponds state sail) (rs2 rs1 rd : RV32I.Register) :
    DecodedRtypeSimulation state sail .XOR rs2 rs1 rd :=
  decoded_rtype_state_simulation h .XOR rs2 rs1 rd

theorem decoded_srl_state_simulation {state : RV32I.State} {sail : SailState}
    (h : StateCorresponds state sail) (rs2 rs1 rd : RV32I.Register) :
    DecodedRtypeSimulation state sail .SRL rs2 rs1 rd :=
  decoded_rtype_state_simulation h .SRL rs2 rs1 rd

theorem decoded_sra_state_simulation {state : RV32I.State} {sail : SailState}
    (h : StateCorresponds state sail) (rs2 rs1 rd : RV32I.Register) :
    DecodedRtypeSimulation state sail .SRA rs2 rs1 rd :=
  decoded_rtype_state_simulation h .SRA rs2 rs1 rd

theorem decoded_or_state_simulation {state : RV32I.State} {sail : SailState}
    (h : StateCorresponds state sail) (rs2 rs1 rd : RV32I.Register) :
    DecodedRtypeSimulation state sail .OR rs2 rs1 rd :=
  decoded_rtype_state_simulation h .OR rs2 rs1 rd

theorem decoded_and_state_simulation {state : RV32I.State} {sail : SailState}
    (h : StateCorresponds state sail) (rs2 rs1 rd : RV32I.Register) :
    DecodedRtypeSimulation state sail .AND rs2 rs1 rd :=
  decoded_rtype_state_simulation h .AND rs2 rs1 rd

/-- Four initialized generated memory bytes holding one little-endian RV32I
word at the selected Bare physical address. -/
def SailWordAt (sail : SailState) (address : RV32I.Address)
    (value : RV32I.Word) : Prop :=
  let physical := (sailPhysicalAddress address).toNat
  sail.mem.get? physical = some (value.extractLsb' 0 8) ∧
  sail.mem.get? (physical + 1) = some (value.extractLsb' 8 8) ∧
  sail.mem.get? ((physical + 1) + 1) = some (value.extractLsb' 16 8) ∧
  sail.mem.get? (((physical + 1) + 1) + 1) =
    some (value.extractLsb' 24 8)

theorem sailReadRamAction_word_of_bytes {sail : SailState}
    {address : RV32I.Address} {value : RV32I.Word}
    (present : SailWordAt sail address value) :
    sailReadRamAction address .word sail = .ok (value, ()) sail := by
  rcases present with ⟨h0, h1, h2, h3⟩
  have read0 : (Sail.ConcurrencyInterfaceV1.PreSail.readByte
      (sailPhysicalAddress address).toNat : LeanRV32D.SailM (BitVec 8)) sail =
      .ok (value.extractLsb' 0 8) sail := by
    simp only [Sail.ConcurrencyInterfaceV1.PreSail.readByte,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind]
    rw [h0]
    rfl
  have read1 : (Sail.ConcurrencyInterfaceV1.PreSail.readByte
      ((sailPhysicalAddress address).toNat + 1) :
        LeanRV32D.SailM (BitVec 8)) sail =
      .ok (value.extractLsb' 8 8) sail := by
    simp only [Sail.ConcurrencyInterfaceV1.PreSail.readByte,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind]
    rw [h1]
    rfl
  have read2 : (Sail.ConcurrencyInterfaceV1.PreSail.readByte
      ((sailPhysicalAddress address).toNat + 1 + 1) :
        LeanRV32D.SailM (BitVec 8)) sail =
      .ok (value.extractLsb' 16 8) sail := by
    simp only [Sail.ConcurrencyInterfaceV1.PreSail.readByte,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind]
    rw [h2]
    rfl
  have read3 : (Sail.ConcurrencyInterfaceV1.PreSail.readByte
      ((sailPhysicalAddress address).toNat + 1 + 1 + 1) :
        LeanRV32D.SailM (BitVec 8)) sail =
      .ok (value.extractLsb' 24 8) sail := by
    simp only [Sail.ConcurrencyInterfaceV1.PreSail.readByte,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind]
    rw [h3]
    rfl
  have readBytes1 : (Sail.ConcurrencyInterfaceV1.PreSail.readBytes 1
      ((((sailPhysicalAddress address).toNat + 1) + 1) + 1) :
        LeanRV32D.SailM (BitVec 8 × Option Bool)) sail =
      .ok (value.extractLsb' 24 8, none) sail := by
    rw [Sail.ConcurrencyInterfaceV1.PreSail.readBytes]
    simp only [bind, EStateM.bind]
    rw [read3]
    rfl
  have readBytes2 : (Sail.ConcurrencyInterfaceV1.PreSail.readBytes 2
      (((sailPhysicalAddress address).toNat + 1) + 1) :
        LeanRV32D.SailM (BitVec 16 × Option Bool)) sail =
      .ok (value.extractLsb' 24 8 ++ value.extractLsb' 16 8, none) sail := by
    rw [Sail.ConcurrencyInterfaceV1.PreSail.readBytes]
    simp only [bind, EStateM.bind, read2, readBytes1, pure, EStateM.pure]
    case x => exact by decide
    rfl
  have readBytes3 : (Sail.ConcurrencyInterfaceV1.PreSail.readBytes 3
      ((sailPhysicalAddress address).toNat + 1) :
        LeanRV32D.SailM (BitVec 24 × Option Bool)) sail =
      .ok ((value.extractLsb' 24 8 ++ value.extractLsb' 16 8) ++
        value.extractLsb' 8 8, none) sail := by
    rw [Sail.ConcurrencyInterfaceV1.PreSail.readBytes]
    simp only [bind, EStateM.bind, read1, readBytes2, pure, EStateM.pure]
    case x => exact by decide
    rfl
  have readBytes : (Sail.ConcurrencyInterfaceV1.PreSail.readBytes 4
      (sailPhysicalAddress address).toNat :
        LeanRV32D.SailM (BitVec 32 × Option Bool)) sail =
      .ok (value, none) sail := by
    rw [Sail.ConcurrencyInterfaceV1.PreSail.readBytes]
    simp only [bind, EStateM.bind, read0, readBytes3, pure, EStateM.pure]
    case x => exact by decide
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
      (start₂ := 24) (start₁ := 16) (len₁ := 8) (len₂ := 8) rfl]
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb'
      (start₂ := 16) (start₁ := 8) (len₁ := 8) (len₂ := 16) rfl]
    change EStateM.Result.ok
      (value.extractLsb' 8 24 ++ value.extractLsb' 0 8, none) sail = _
    rw [@BitVec.extractLsb'_append_extractLsb' 24 8 value]
  have memRead : (@LeanRV32D.ConcurrencyInterfaceV1.sail_mem_read
      4 64 34 Unit LeanRV32D.RISCV_strong_access
      LeanRV32D.instArch_leanRV32D (sailReadRequest address .word)) sail =
      .ok (.Ok (value, none)) sail := by
    simp only [LeanRV32D.ConcurrencyInterfaceV1.sail_mem_read,
      Sail.ConcurrencyInterfaceV1.PreSail.sail_mem_read, sailReadRequest]
    change EStateM.map Sail.Ok
      (Sail.ConcurrencyInterfaceV1.PreSail.readBytes 4
        (sailPhysicalAddress address).toNat) sail = _
    simp only [EStateM.map, readBytes]
  simp only [sailReadRamAction, RV32I.AccessWidth.bytes,
    bind, EStateM.bind, memRead]
  rfl

/-! ## Decoded LW: aligned successful ordinary RAM profile -/

/-- The clean effective address selected by decoded `LW`. -/
def cleanLwAddress (state : RV32I.State) (immediate : BitVec 12)
    (rs1 : RV32I.Register) : RV32I.Address :=
  RV32I.Instruction.address immediate (state.readRegister rs1)

/-- The clean architectural post-state after a successful word load. -/
def cleanLwPost (state : RV32I.State) (rd : RV32I.Register)
    (value : RV32I.Word) : RV32I.State :=
  { state.writeRegister rd value with pc := RV32I.nextPc state }

/-- State after the generated sequential-PC staging operation shared by
decoded base instructions. -/
def sailSequentialStaged (sail : SailState) (state : RV32I.State) : SailState :=
  sailSetReg sail LeanRV32D.Register.nextPC (RV32I.nextPc state)

/-- LW-specific compatibility name for the shared staged state. -/
abbrev sailLwStaged := sailSequentialStaged

/-- Generated post-state after the load destination write and PC commitment. -/
def sailLwPost (sail : SailState) (state : RV32I.State)
    (rd : RV32I.Register) (value : RV32I.Word) : SailState :=
  sailSetReg (sailWriteX (sailLwStaged sail state) rd value)
    LeanRV32D.Register.PC (RV32I.nextPc state)

/-- Reviewable ordinary-memory replacement for the generated virtual-memory
entry point. It deliberately retains Sail's own source-register read and its
32-bit addition; only the platform/privileged path below that calculation is
collapsed to the exact plain RAM request proved above. -/
def sailOrdinaryLwRead (rs1 : RV32I.Register) (offset : RV32I.Word) :
    LeanRV32D.SailM (Sail.Result RV32I.Word LeanRV32D.ExecutionResult) := do
  let base ← rX_bits (sailRegister rs1)
  let (value, ()) ← sailReadRamAction (base + offset) .word
  pure (.Ok value)

/-- The one generated-path assumption used by the successful ordinary-RAM
theorem, stated at the exact staged pre-state. It says that `vmem_read` takes
the reviewed Bare, permitted, unsplit, non-MMIO route. It bundles only the
generated privilege/translation, pointer-masking, PMA/PMP, routing, and
platform checks needed to reach `read_ram Read_plain`; byte initialization is
kept separate in `SailWordAt` and proved rather than assumed as a result. -/
def GeneratedOrdinaryLwPath (sail : SailState) (state : RV32I.State)
    (immediate : BitVec 12) (rs1 : RV32I.Register) : Prop :=
  LeanRV32D.Functions.vmem_read (sailRegister rs1)
      (sign_extend immediate) 4 (.Load .Data) false false false
      (sailLwStaged sail state) =
    sailOrdinaryLwRead rs1 (sign_extend immediate)
      (sailLwStaged sail state)

/-- The selected generated instruction fragment: stage sequential `nextPC`,
run the actual generated `execute_LOAD imm rs1 rd false 4`, then perform the
same `tick_pc` commitment used by the ADDI bridge. -/
noncomputable def sailDecodedLwStep (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) : LeanRV32D.SailM LeanRV32D.ExecutionResult := do
  stageSequentialPc
  let result ← LeanRV32D.Functions.execute_LOAD immediate
    (sailRegister rs1) (sailRegister rd) false 4
  tick_pc ()
  pure result

/-- Clean and generated LW use the same sign extension and 32-bit wrapping
addition for the effective address. -/
theorem lw_effective_address_eq_sail (state : RV32I.State)
    (immediate : BitVec 12) (rs1 : RV32I.Register) :
    cleanLwAddress state immediate rs1 =
      state.readRegister rs1 + sign_extend immediate := by
  simp [cleanLwAddress, RV32I.Instruction.address, sign_extend,
    Sail.BitVec.signExtend]

theorem lw_request_corresponds (state : RV32I.State)
    (immediate : BitVec 12) (rs1 : RV32I.Register) :
    DataRequestCorresponds
      (.load (cleanLwAddress state immediate rs1) .word)
      (.read .word
        (sailReadRequest (cleanLwAddress state immediate rs1) .word)) := by
  exact .load _ _

@[simp] theorem sailLwStaged_mem (sail : SailState) (state : RV32I.State) :
    (sailLwStaged sail state).mem = sail.mem := by
  rfl

@[simp] theorem sailWriteX_mem (sail : SailState) (rd : RV32I.Register)
    (value : RV32I.Word) :
    (sailWriteX sail rd value).mem = sail.mem := by
  unfold sailWriteX
  split <;> rfl

@[simp] theorem sailLwPost_mem (sail : SailState) (state : RV32I.State)
    (rd : RV32I.Register) (value : RV32I.Word) :
    (sailLwPost sail state rd value).mem = sail.mem := by
  change (sailWriteX (sailLwStaged sail state) rd value).mem = sail.mem
  rw [sailWriteX_mem, sailLwStaged_mem]

theorem sailWordAt_staged {sail : SailState} {state : RV32I.State}
    {address : RV32I.Address} {value : RV32I.Word}
    (present : SailWordAt sail address value) :
    SailWordAt (sailLwStaged sail state) address value := by
  simpa [SailWordAt, sailSequentialStaged, sailSetReg] using present

theorem sailOrdinaryLwRead_word {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (immediate : BitVec 12)
    (rs1 : RV32I.Register) (value : RV32I.Word)
    (present : SailWordAt sail (cleanLwAddress state immediate rs1) value) :
    sailOrdinaryLwRead rs1 (sign_extend immediate)
        (sailLwStaged sail state) =
      .ok (.Ok value) (sailLwStaged sail state) := by
  have stagedRelation := corresponds.stageNextPc
  have stagedCorresponds : StateCorresponds state (sailLwStaged sail state) :=
    { pc := stagedRelation.pc
      register := stagedRelation.register }
  have readSource := rX_bits_of_corresponds stagedCorresponds rs1
  have addressEq := lw_effective_address_eq_sail state immediate rs1
  have bytes := sailReadRamAction_word_of_bytes
    (sailWordAt_staged (state := state) present)
  simp only [sailOrdinaryLwRead, bind, EStateM.bind, readSource]
  rw [← addressEq, bytes]
  rfl

/-- Under the single reviewed path equation and concrete byte initialization,
the actual generated `execute_LOAD` writes the loaded word and retires. The
false signedness flag is harmless for width four because sign extension from
32 bits to XLEN=32 is the identity. -/
theorem execute_LOAD_lw_word {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) (value : RV32I.Word)
    (path : GeneratedOrdinaryLwPath sail state immediate rs1)
    (present : SailWordAt sail (cleanLwAddress state immediate rs1) value) :
    LeanRV32D.Functions.execute_LOAD immediate (sailRegister rs1)
        (sailRegister rd) false 4 (sailLwStaged sail state) =
      .ok (.Retire_Success ())
        (sailWriteX (sailLwStaged sail state) rd value) := by
  have readResult : LeanRV32D.Functions.vmem_read (sailRegister rs1)
      (sign_extend immediate) 4 (.Load .Data) false false false
      (sailLwStaged sail state) =
      .ok (.Ok value) (sailLwStaged sail state) := by
    rw [path]
    exact sailOrdinaryLwRead_word corresponds immediate rs1 value present
  have writeResult := wX_bits_sailRegister
    (sailLwStaged sail state) rd value
  have extendResult : LeanRV32D.Functions.extend_value false value = value := by
    simp [LeanRV32D.Functions.extend_value, sign_extend,
      Sail.BitVec.signExtend]
  simp [LeanRV32D.Functions.execute_LOAD, readResult, writeResult,
    extendResult, LeanRV32D.Functions.RETIRE_SUCCESS, LeanRV32D.assert,
    Sail.ConcurrencyInterfaceV1.PreSail.assert,
    LeanRV32D.Functions.xlen_bytes, bind, EStateM.bind, pure, EStateM.pure]

theorem sailDecodedLwStep_success {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) (value : RV32I.Word)
    (path : GeneratedOrdinaryLwPath sail state immediate rs1)
    (present : SailWordAt sail (cleanLwAddress state immediate rs1) value) :
    sailDecodedLwStep immediate rs1 rd sail =
      .ok (.Retire_Success ()) (sailLwPost sail state rd value) := by
  have stageEq : stageSequentialPc sail =
      .ok () (sailLwStaged sail state) := by
    rw [stageSequentialPc_of_corresponds corresponds]
    exact writeReg_eq_set sail (r := LeanRV32D.Register.nextPC)
      (RV32I.nextPc state)
  have executeEq := execute_LOAD_lw_word corresponds immediate rs1 rd value
    path present
  have nextPcFound :
      (sailWriteX (sailLwStaged sail state) rd value).regs.get?
          LeanRV32D.Register.nextPC = some (RV32I.nextPc state) := by
    rw [sailWriteX_nextPc]
    simp [sailSequentialStaged, sailSetReg,
      Std.ExtDHashMap.get?_insert]
  have tickEq := tick_pc_of_nextPc nextPcFound
  simp only [sailDecodedLwStep, bind, EStateM.bind, stageEq, executeEq,
    tickEq]
  rfl

theorem sailLwPost_corresponds {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (rd : RV32I.Register)
    (value : RV32I.Word) :
    StateCorresponds (cleanLwPost state rd value)
      (sailLwPost sail state rd value) := by
  have stagedRelation := corresponds.stageNextPc
  have stagedCorresponds : StateCorresponds state (sailLwStaged sail state) :=
    { pc := stagedRelation.pc
      register := stagedRelation.register }
  have writtenCorresponds := stagedCorresponds.writeX rd value
  have committedCorresponds := writtenCorresponds.setPc (RV32I.nextPc state)
  simpa [cleanLwPost, sailLwPost] using committedCorresponds

theorem cleanLwPost_readRegister (state : RV32I.State)
    (rd r : RV32I.Register) (value : RV32I.Word) :
    (cleanLwPost state rd value).readRegister r =
      if rd.val = 0 then state.readRegister r
      else if r = rd then value else state.readRegister r := by
  exact clean_read_after_write state rd r value

theorem sailLwPost_readRegister {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (rd r : RV32I.Register)
    (value : RV32I.Word) :
    sailReadX (sailLwPost sail state rd value) r =
      some (if rd.val = 0 then state.readRegister r
        else if r = rd then value else state.readRegister r) := by
  rw [(sailLwPost_corresponds corresponds rd value).register r,
    cleanLwPost_readRegister]

theorem sailLwPost_destination {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (rd : RV32I.Register)
    (value : RV32I.Word) (rdNonzero : rd.val ≠ 0) :
    sailReadX (sailLwPost sail state rd value) rd = some value := by
  simp [sailLwPost_readRegister corresponds rd rd value, rdNonzero]

theorem sailLwPost_unaffected {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (rd r : RV32I.Register)
    (value : RV32I.Word) (different : r ≠ rd) :
    sailReadX (sailLwPost sail state rd value) r = sailReadX sail r := by
  rw [sailLwPost_readRegister corresponds rd r value, corresponds.register r]
  simp [different]

theorem sailLwPost_x0 {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (rd : RV32I.Register)
    (value : RV32I.Word) :
    sailReadX (sailLwPost sail state rd value) 0 = some 0 := by
  exact (sailLwPost_corresponds corresponds rd value).register 0

theorem sailLwPost_pc {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (rd : RV32I.Register)
    (value : RV32I.Word) :
    (sailLwPost sail state rd value).regs.get? LeanRV32D.Register.PC =
      some (RV32I.nextPc state) := by
  exact (sailLwPost_corresponds corresponds rd value).pc

theorem cleanLwPost_pc (state : RV32I.State) (rd : RV32I.Register)
    (value : RV32I.Word) :
    (cleanLwPost state rd value).pc = state.pc + 4 := by
  rfl

theorem sailLwPost_pc_plus_four {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (rd : RV32I.Register)
    (value : RV32I.Word) :
    (sailLwPost sail state rd value).regs.get? LeanRV32D.Register.PC =
      some (state.pc + 4) := by
  simpa [RV32I.nextPc] using sailLwPost_pc corresponds rd value

/-- The selected generated platform's callbacks touched by this fragment are
definitionally inert. These facts are configuration facts, not hypotheses of
the simulation theorem. -/
theorem generated_pc_write_callback_noop (value : RV32I.Word) :
    pc_write_callback value = () := rfl

theorem generated_xreg_full_write_callback_noop (name : String)
    (rd : LeanRV32D.regidx) (value : RV32I.Word) :
    xreg_full_write_callback name rd value = () := rfl

theorem generated_memory_read_callback_noop (name : String)
    (address : LeanRV32D.physaddrbits) (width : Nat)
    (value : BitVec (8 * width)) :
    mem_read_callback name address width value = () := rfl

theorem clean_execute_lw (state : RV32I.State) (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) :
    RV32I.execute (.lw rd rs1 immediate) state =
      .request
        (.memory (.load (cleanLwAddress state immediate rs1) .word))
        (RV32I.finishLoad state rd (cleanLwAddress state immediate rs1)
          .word false) := by
  rfl

theorem clean_finishLoad_success (state : RV32I.State)
    (rd : RV32I.Register) (address : RV32I.Address) (value : RV32I.Word) :
    RV32I.finishLoad state rd address .word false (.success value) =
      .done (.retired (cleanLwPost state rd value)) := by
  rfl

/-- A successful clean EEI response records exactly one completed load effect
before returning the same architectural post-state used by the Sail bridge. -/
theorem clean_lw_success_runs {environmentState : Type}
    (environment : RV32I.ExecutionEnvironment environmentState)
    {before after : environmentState} (state : RV32I.State)
    (immediate : BitVec 12) (rs1 rd : RV32I.Register)
    (value : RV32I.Word)
    (responds : environment.responds before
      (.memory (.load (cleanLwAddress state immediate rs1) .word))
      (.success value) after) :
    RV32I.Interaction.Runs environment
      (RV32I.execute (.lw rd rs1 immediate) state) before
      [.memoryAccess
        { request := .load (cleanLwAddress state immediate rs1) .word
          response := .success value }]
      (.retired (cleanLwPost state rd value)) after := by
  rw [clean_execute_lw]
  exact RV32I.Interaction.Runs.request before after after
    (.memory (.load (cleanLwAddress state immediate rs1) .word))
    (.success value)
    (RV32I.finishLoad state rd (cleanLwAddress state immediate rs1)
      .word false)
    [] (.retired (cleanLwPost state rd value)) responds
    (RV32I.Interaction.Runs.done after
      (RV32I.InstructionResult.retired (cleanLwPost state rd value)))

/-- An explicit state-level certificate for the decoded LW bridge. Each field
is intentionally reviewable at the architectural boundary; generated details
remain confined to this package. -/
structure DecodedLwSimulation {environmentState : Type}
    (environment : RV32I.ExecutionEnvironment environmentState)
    (before after : environmentState) (state : RV32I.State)
    (sail : SailState) (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) (value : RV32I.Word) : Prop where
  aligned : RV32I.AccessWidth.word.Aligned
    (cleanLwAddress state immediate rs1)
  effectiveAddress : cleanLwAddress state immediate rs1 =
    state.readRegister rs1 + sign_extend immediate
  requestCorrespondence : DataRequestCorresponds
    (.load (cleanLwAddress state immediate rs1) .word)
    (.read .word
      (sailReadRequest (cleanLwAddress state immediate rs1) .word))
  cleanExecution : RV32I.execute (.lw rd rs1 immediate) state =
    .request
      (.memory (.load (cleanLwAddress state immediate rs1) .word))
      (RV32I.finishLoad state rd (cleanLwAddress state immediate rs1)
        .word false)
  cleanRun : RV32I.Interaction.Runs environment
    (RV32I.execute (.lw rd rs1 immediate) state) before
    [.memoryAccess
      { request := .load (cleanLwAddress state immediate rs1) .word
        response := .success value }]
    (.retired (cleanLwPost state rd value)) after
  sailExecution : sailDecodedLwStep immediate rs1 rd sail =
    .ok (.Retire_Success ()) (sailLwPost sail state rd value)
  postCorrespondence : StateCorresponds (cleanLwPost state rd value)
    (sailLwPost sail state rd value)
  destination : rd.val ≠ 0 →
    sailReadX (sailLwPost sail state rd value) rd = some value
  unaffected : ∀ r : RV32I.Register, r ≠ rd →
    sailReadX (sailLwPost sail state rd value) r = sailReadX sail r
  x0 : sailReadX (sailLwPost sail state rd value) 0 = some 0
  pc : (sailLwPost sail state rd value).regs.get?
    LeanRV32D.Register.PC = some (state.pc + 4)
  memory : (sailLwPost sail state rd value).mem = sail.mem

/-- Main decoded-LW simulation theorem for a naturally aligned, successful
ordinary-memory word read in the selected Bare profile. -/
theorem decoded_lw_state_simulation {environmentState : Type}
    (environment : RV32I.ExecutionEnvironment environmentState)
    {before after : environmentState} {state : RV32I.State}
    {sail : SailState} (corresponds : StateCorresponds state sail)
    (immediate : BitVec 12) (rs1 rd : RV32I.Register)
    (value : RV32I.Word)
    (aligned : RV32I.AccessWidth.word.Aligned
      (cleanLwAddress state immediate rs1))
    (path : GeneratedOrdinaryLwPath sail state immediate rs1)
    (present : SailWordAt sail (cleanLwAddress state immediate rs1) value)
    (responds : environment.responds before
      (.memory (.load (cleanLwAddress state immediate rs1) .word))
      (.success value) after) :
    DecodedLwSimulation environment before after state sail immediate
      rs1 rd value where
  aligned := aligned
  effectiveAddress := lw_effective_address_eq_sail state immediate rs1
  requestCorrespondence := lw_request_corresponds state immediate rs1
  cleanExecution := clean_execute_lw state immediate rs1 rd
  cleanRun := clean_lw_success_runs environment state immediate rs1 rd value
    responds
  sailExecution := sailDecodedLwStep_success corresponds immediate rs1 rd
    value path present
  postCorrespondence := sailLwPost_corresponds corresponds rd value
  destination := sailLwPost_destination corresponds rd value
  unaffected := fun r => sailLwPost_unaffected corresponds rd r value
  x0 := sailLwPost_x0 corresponds rd value
  pc := sailLwPost_pc_plus_four corresponds rd value
  memory := sailLwPost_mem sail state rd value

/-! ## Decoded SW: aligned successful ordinary RAM profile -/

/-- The exact sequential generated state after writing one little-endian word
at a Bare physical address. The four insertions are in increasing address
order, matching Lean Sail's `writeBytes`. -/
def sailWriteWordState (sail : SailState) (address : RV32I.Address)
    (value : RV32I.Word) : SailState :=
  let physical := (sailPhysicalAddress address).toNat
  let memory0 := sail.mem.insert physical (value.extractLsb' 0 8)
  let memory1 := memory0.insert (physical + 1) (value.extractLsb' 8 8)
  let memory2 := memory1.insert (physical + 2) (value.extractLsb' 16 8)
  let memory3 := memory2.insert (physical + 3) (value.extractLsb' 24 8)
  { sail with mem := memory3 }

/-- The generated sequential backend writes a word as exactly four
little-endian byte insertions. No initial contents are needed for a total hash
map write. -/
theorem sailWriteBytes_word (sail : SailState) (address : RV32I.Address)
    (value : RV32I.Word) :
    (Sail.ConcurrencyInterfaceV1.PreSail.writeBytes (n := 4)
      (sailPhysicalAddress address).toNat value : LeanRV32D.SailM Bool) sail =
      .ok true (sailWriteWordState sail address value) := by
  simp [Sail.ConcurrencyInterfaceV1.PreSail.writeBytes,
    Sail.ConcurrencyInterfaceV1.PreSail.writeByte,
    List.ofFn_succ, modify, MonadState.modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet,
    bind, EStateM.bind, pure, EStateM.pure,
    sailWriteWordState]

@[simp] theorem sailWriteWordState_byte0 (sail : SailState)
    (address : RV32I.Address) (value : RV32I.Word) :
    (sailWriteWordState sail address value).mem.get?
        (sailPhysicalAddress address).toNat =
      some (value.extractLsb' 0 8) := by
  simp [sailWriteWordState, Std.ExtHashMap.get?, Std.ExtHashMap.insert,
    Std.ExtDHashMap.Const.get?_insert]

@[simp] theorem sailWriteWordState_byte1 (sail : SailState)
    (address : RV32I.Address) (value : RV32I.Word) :
    (sailWriteWordState sail address value).mem.get?
        ((sailPhysicalAddress address).toNat + 1) =
      some (value.extractLsb' 8 8) := by
  simp [sailWriteWordState, Std.ExtHashMap.get?, Std.ExtHashMap.insert,
    Std.ExtDHashMap.Const.get?_insert]

@[simp] theorem sailWriteWordState_byte2 (sail : SailState)
    (address : RV32I.Address) (value : RV32I.Word) :
    (sailWriteWordState sail address value).mem.get?
        ((sailPhysicalAddress address).toNat + 2) =
      some (value.extractLsb' 16 8) := by
  simp [sailWriteWordState, Std.ExtHashMap.get?, Std.ExtHashMap.insert,
    Std.ExtDHashMap.Const.get?_insert]

@[simp] theorem sailWriteWordState_byte3 (sail : SailState)
    (address : RV32I.Address) (value : RV32I.Word) :
    (sailWriteWordState sail address value).mem.get?
        ((sailPhysicalAddress address).toNat + 3) =
      some (value.extractLsb' 24 8) := by
  simp [sailWriteWordState, Std.ExtHashMap.get?, Std.ExtHashMap.insert]

/-- Every byte outside the four addressed locations is unchanged. Together
with `sailWriteWordState_byte0`--`byte3`, this states that exactly those four
map entries are updated. -/
theorem sailWriteWordState_outside (sail : SailState)
    (address : RV32I.Address) (value : RV32I.Word) (observed : Nat)
    (h0 : observed ≠ (sailPhysicalAddress address).toNat)
    (h1 : observed ≠ (sailPhysicalAddress address).toNat + 1)
    (h2 : observed ≠ (sailPhysicalAddress address).toNat + 2)
    (h3 : observed ≠ (sailPhysicalAddress address).toNat + 3) :
    (sailWriteWordState sail address value).mem.get? observed =
      sail.mem.get? observed := by
  simp only [sailWriteWordState, Std.ExtHashMap.get?,
    Std.ExtHashMap.insert, Std.ExtDHashMap.Const.get?_insert, beq_iff_eq]
  rw [if_neg (Ne.symm h3), if_neg (Ne.symm h2),
    if_neg (Ne.symm h1), if_neg (Ne.symm h0)]

/-- The exact generated plain-write action succeeds and produces precisely
the four-byte state above. Backend success and addressed-map insertion are
proved here, not supplied as simulation assumptions. -/
theorem sailWriteRamAction_word (sail : SailState)
    (address : RV32I.Address) (value : RV32I.Word) :
    sailWriteRamAction address .word value sail =
      .ok true (sailWriteWordState sail address value) := by
  have writeBytes := sailWriteBytes_word sail address value
  have memWrite : (@LeanRV32D.ConcurrencyInterfaceV1.sail_mem_write
      4 64 34 Unit LeanRV32D.RISCV_strong_access
      LeanRV32D.instArch_leanRV32D
      (sailWriteRequest address .word value)) sail =
      .ok (.Ok (some true)) (sailWriteWordState sail address value) := by
    simp only [LeanRV32D.ConcurrencyInterfaceV1.sail_mem_write,
      Sail.ConcurrencyInterfaceV1.PreSail.sail_mem_write, sailWriteRequest]
    have converted : toSailAccessValue .word value = value := rfl
    rw [converted]
    simp only [bind, EStateM.bind]
    simp only [pure, EStateM.pure]
    exact congrArg (fun result :
        EStateM.Result (Sail.Error LeanRV32D.exception) SailState Bool =>
      (match result with
       | .ok byteSuccess next =>
           EStateM.Result.ok (Sail.Ok (some byteSuccess)) next
       | .error error next => EStateM.Result.error error next :
        EStateM.Result (Sail.Error LeanRV32D.exception) SailState
          (Sail.Result (Option Bool)
            Sail.ConcurrencyInterfaceV1.Arch.abort))) writeBytes
  simp only [sailWriteRamAction, RV32I.AccessWidth.bytes,
    bind, EStateM.bind, memWrite]
  rfl

/-- The clean effective address selected by decoded `SW`. -/
def cleanSwAddress (state : RV32I.State) (immediate : BitVec 12)
    (rs1 : RV32I.Register) : RV32I.Address :=
  RV32I.Instruction.address immediate (state.readRegister rs1)

/-- The clean word payload selected from `rs2`. -/
def cleanSwValue (state : RV32I.State) (rs2 : RV32I.Register) : RV32I.Word :=
  state.readRegister rs2

/-- Successful SW changes no integer register and advances only PC. -/
def cleanSwPost (state : RV32I.State) : RV32I.State :=
  { state with pc := RV32I.nextPc state }

/-- Generated state after the staged instruction performs its four-byte RAM
write, before `tick_pc` commits PC. -/
def sailSwWritten (sail : SailState) (state : RV32I.State)
    (immediate : BitVec 12) (rs2 rs1 : RV32I.Register) : SailState :=
  sailWriteWordState (sailSequentialStaged sail state)
    (cleanSwAddress state immediate rs1) (cleanSwValue state rs2)

/-- Generated post-state after the successful write and PC commitment. -/
def sailSwPost (sail : SailState) (state : RV32I.State)
    (immediate : BitVec 12) (rs2 rs1 : RV32I.Register) : SailState :=
  sailSetReg (sailSwWritten sail state immediate rs2 rs1)
    LeanRV32D.Register.PC (RV32I.nextPc state)

/-- Reviewable ordinary-memory replacement below generated `vmem_write`.
Sail's source-register read and 32-bit address addition remain explicit; the
platform/privileged machinery alone is collapsed to the exact plain RAM
action. -/
def sailOrdinarySwWrite (rs1 : RV32I.Register) (offset value : RV32I.Word) :
    LeanRV32D.SailM (Sail.Result Bool LeanRV32D.ExecutionResult) := do
  let base ← rX_bits (sailRegister rs1)
  let success ← sailWriteRamAction (base + offset) .word value
  pure (.Ok success)

/-- The sole generated-path premise for successful ordinary-RAM SW. At the
exact staged state it selects unchanged pointer masking, Bare translation,
PMA/PMP acceptance, one unsplit access, and non-MMIO RAM routing. Backend
success and byte updates are not assumed; they are proved by
`sailWriteRamAction_word`. -/
def GeneratedOrdinarySwPath (sail : SailState) (state : RV32I.State)
    (immediate : BitVec 12) (rs2 rs1 : RV32I.Register) : Prop :=
  LeanRV32D.Functions.vmem_write (sailRegister rs1)
      (sign_extend immediate) 4 (cleanSwValue state rs2)
      (.Store .Data) false false false (sailSequentialStaged sail state) =
    sailOrdinarySwWrite rs1 (sign_extend immediate) (cleanSwValue state rs2)
      (sailSequentialStaged sail state)

/-- The selected generated instruction fragment uses the actual
`execute_STORE imm rs2 rs1 4`, with shared sequential staging and commitment. -/
noncomputable def sailDecodedSwStep (immediate : BitVec 12)
    (rs2 rs1 : RV32I.Register) : LeanRV32D.SailM LeanRV32D.ExecutionResult := do
  stageSequentialPc
  let result ← LeanRV32D.Functions.execute_STORE immediate
    (sailRegister rs2) (sailRegister rs1) 4
  tick_pc ()
  pure result

theorem sw_effective_address_eq_sail (state : RV32I.State)
    (immediate : BitVec 12) (rs1 : RV32I.Register) :
    cleanSwAddress state immediate rs1 =
      state.readRegister rs1 + sign_extend immediate := by
  simp [cleanSwAddress, RV32I.Instruction.address, sign_extend,
    Sail.BitVec.signExtend]

theorem sw_source_value_eq_sail (state : RV32I.State)
    (rs2 : RV32I.Register) :
    cleanSwValue state rs2 = state.readRegister rs2 := rfl

theorem sw_request_corresponds (state : RV32I.State)
    (immediate : BitVec 12) (rs2 rs1 : RV32I.Register) :
    DataRequestCorresponds
      (.store (cleanSwAddress state immediate rs1) .word
        (cleanSwValue state rs2))
      (.write .word (sailWriteRequest
        (cleanSwAddress state immediate rs1) .word
        (cleanSwValue state rs2))) := by
  exact .store _ _ _

@[simp] theorem sailWriteWordState_regs (sail : SailState)
    (address : RV32I.Address) (value : RV32I.Word) :
    (sailWriteWordState sail address value).regs = sail.regs := by
  rfl

theorem StateCorresponds.writeWordMemory {clean : RV32I.State}
    {sail : SailState} (corresponds : StateCorresponds clean sail)
    (address : RV32I.Address) (value : RV32I.Word) :
    StateCorresponds clean (sailWriteWordState sail address value) := by
  constructor
  · simpa [sailWriteWordState] using corresponds.pc
  · intro r
    simpa [sailReadX, sailReadKey, sailWriteWordState] using
      corresponds.register r

theorem sailOrdinarySwWrite_word {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (immediate : BitVec 12)
    (rs2 rs1 : RV32I.Register) :
    sailOrdinarySwWrite rs1 (sign_extend immediate) (cleanSwValue state rs2)
        (sailSequentialStaged sail state) =
      .ok (.Ok true) (sailSwWritten sail state immediate rs2 rs1) := by
  have stagedRelation := corresponds.stageNextPc
  have stagedCorresponds :
      StateCorresponds state (sailSequentialStaged sail state) :=
    { pc := stagedRelation.pc
      register := stagedRelation.register }
  have readBase := rX_bits_of_corresponds stagedCorresponds rs1
  have addressEq := sw_effective_address_eq_sail state immediate rs1
  have writeResult := sailWriteRamAction_word
    (sailSequentialStaged sail state) (cleanSwAddress state immediate rs1)
    (cleanSwValue state rs2)
  simp only [sailOrdinarySwWrite, bind, EStateM.bind, readBase]
  rw [← addressEq, writeResult]
  rfl

theorem sw_staged_source_read {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (rs2 : RV32I.Register) :
    rX_bits (sailRegister rs2) (sailSequentialStaged sail state) =
      .ok (cleanSwValue state rs2) (sailSequentialStaged sail state) := by
  have stagedRelation := corresponds.stageNextPc
  have stagedCorresponds :
      StateCorresponds state (sailSequentialStaged sail state) :=
    { pc := stagedRelation.pc
      register := stagedRelation.register }
  exact rX_bits_of_corresponds stagedCorresponds rs2

/-- The actual generated store executor reads the corresponding `rs2` word,
writes it through the selected ordinary path, and retires successfully. -/
theorem execute_STORE_sw_word {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (immediate : BitVec 12)
    (rs2 rs1 : RV32I.Register)
    (path : GeneratedOrdinarySwPath sail state immediate rs2 rs1) :
    LeanRV32D.Functions.execute_STORE immediate (sailRegister rs2)
        (sailRegister rs1) 4 (sailSequentialStaged sail state) =
      .ok (.Retire_Success ())
        (sailSwWritten sail state immediate rs2 rs1) := by
  have readSource := sw_staged_source_read corresponds rs2
  have extracted : Sail.BitVec.extractLsb (cleanSwValue state rs2) 31 0 =
      cleanSwValue state rs2 := by
    apply BitVec.eq_of_toNat_eq
    simp [Sail.BitVec.extractLsb]
    exact (cleanSwValue state rs2).isLt
  have writeResult : LeanRV32D.Functions.vmem_write (sailRegister rs1)
      (sign_extend immediate) 4 (cleanSwValue state rs2)
      (.Store .Data) false false false (sailSequentialStaged sail state) =
      .ok (.Ok true) (sailSwWritten sail state immediate rs2 rs1) := by
    rw [path]
    exact sailOrdinarySwWrite_word corresponds immediate rs2 rs1
  simp [LeanRV32D.Functions.execute_STORE, readSource, extracted, writeResult,
    LeanRV32D.Functions.RETIRE_SUCCESS, LeanRV32D.assert,
    Sail.ConcurrencyInterfaceV1.PreSail.assert,
    LeanRV32D.Functions.xlen_bytes, bind, EStateM.bind, pure, EStateM.pure]

theorem sailDecodedSwStep_success {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (immediate : BitVec 12)
    (rs2 rs1 : RV32I.Register)
    (path : GeneratedOrdinarySwPath sail state immediate rs2 rs1) :
    sailDecodedSwStep immediate rs2 rs1 sail =
      .ok (.Retire_Success ()) (sailSwPost sail state immediate rs2 rs1) := by
  have stageEq : stageSequentialPc sail =
      .ok () (sailSequentialStaged sail state) := by
    rw [stageSequentialPc_of_corresponds corresponds]
    exact writeReg_eq_set sail (r := LeanRV32D.Register.nextPC)
      (RV32I.nextPc state)
  have executeEq := execute_STORE_sw_word corresponds immediate rs2 rs1 path
  have nextPcFound :
      (sailSwWritten sail state immediate rs2 rs1).regs.get?
          LeanRV32D.Register.nextPC = some (RV32I.nextPc state) := by
    change (sailSequentialStaged sail state).regs.get?
      LeanRV32D.Register.nextPC = some (RV32I.nextPc state)
    simp [sailSequentialStaged, sailSetReg]
  have tickEq := tick_pc_of_nextPc nextPcFound
  simp only [sailDecodedSwStep, bind, EStateM.bind, stageEq, executeEq,
    tickEq]
  rfl

theorem sailSwPost_corresponds {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (immediate : BitVec 12)
    (rs2 rs1 : RV32I.Register) :
    StateCorresponds (cleanSwPost state)
      (sailSwPost sail state immediate rs2 rs1) := by
  have stagedRelation := corresponds.stageNextPc
  have stagedCorresponds :
      StateCorresponds state (sailSequentialStaged sail state) :=
    { pc := stagedRelation.pc
      register := stagedRelation.register }
  have writtenCorresponds := stagedCorresponds.writeWordMemory
    (cleanSwAddress state immediate rs1) (cleanSwValue state rs2)
  have committedCorresponds := writtenCorresponds.setPc (RV32I.nextPc state)
  simpa [cleanSwPost, sailSwPost, sailSwWritten] using committedCorresponds

theorem sailSwPost_register (state : RV32I.State) (sail : SailState)
    (corresponds : StateCorresponds state sail) (immediate : BitVec 12)
    (rs2 rs1 r : RV32I.Register) :
    sailReadX (sailSwPost sail state immediate rs2 rs1) r =
      sailReadX sail r := by
  rw [(sailSwPost_corresponds corresponds immediate rs2 rs1).register r,
    corresponds.register r]
  rfl

theorem sailSwPost_x0 (state : RV32I.State) (sail : SailState)
    (corresponds : StateCorresponds state sail) (immediate : BitVec 12)
    (rs2 rs1 : RV32I.Register) :
    sailReadX (sailSwPost sail state immediate rs2 rs1) 0 = some 0 := by
  exact (sailSwPost_corresponds corresponds immediate rs2 rs1).register 0

theorem sailSwPost_pc_plus_four {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (immediate : BitVec 12)
    (rs2 rs1 : RV32I.Register) :
    (sailSwPost sail state immediate rs2 rs1).regs.get?
        LeanRV32D.Register.PC = some (state.pc + 4) := by
  simpa [cleanSwPost, RV32I.nextPc] using
    (sailSwPost_corresponds corresponds immediate rs2 rs1).pc

/-- Memory correspondence for the clean store effect: the generated post-map
is exactly the four little-endian insertions denoted by that effect. The clean
architectural `State` intentionally contains no memory component. -/
def StoreMemoryCorresponds (before after : SailState)
    (address : RV32I.Address) (value : RV32I.Word) : Prop :=
  after.mem = (sailWriteWordState before address value).mem

theorem sailSwPost_memory_corresponds (sail : SailState) (state : RV32I.State)
    (immediate : BitVec 12) (rs2 rs1 : RV32I.Register) :
    StoreMemoryCorresponds sail (sailSwPost sail state immediate rs2 rs1)
      (cleanSwAddress state immediate rs1) (cleanSwValue state rs2) := by
  rfl

theorem sailSwPost_byte0 (sail : SailState) (state : RV32I.State)
    (immediate : BitVec 12) (rs2 rs1 : RV32I.Register) :
    (sailSwPost sail state immediate rs2 rs1).mem.get?
        (sailPhysicalAddress (cleanSwAddress state immediate rs1)).toNat =
      some ((cleanSwValue state rs2).extractLsb' 0 8) := by
  exact sailWriteWordState_byte0 sail _ _

theorem sailSwPost_byte1 (sail : SailState) (state : RV32I.State)
    (immediate : BitVec 12) (rs2 rs1 : RV32I.Register) :
    (sailSwPost sail state immediate rs2 rs1).mem.get?
        ((sailPhysicalAddress (cleanSwAddress state immediate rs1)).toNat + 1) =
      some ((cleanSwValue state rs2).extractLsb' 8 8) := by
  exact sailWriteWordState_byte1 sail _ _

theorem sailSwPost_byte2 (sail : SailState) (state : RV32I.State)
    (immediate : BitVec 12) (rs2 rs1 : RV32I.Register) :
    (sailSwPost sail state immediate rs2 rs1).mem.get?
        ((sailPhysicalAddress (cleanSwAddress state immediate rs1)).toNat + 2) =
      some ((cleanSwValue state rs2).extractLsb' 16 8) := by
  exact sailWriteWordState_byte2 sail _ _

theorem sailSwPost_byte3 (sail : SailState) (state : RV32I.State)
    (immediate : BitVec 12) (rs2 rs1 : RV32I.Register) :
    (sailSwPost sail state immediate rs2 rs1).mem.get?
        ((sailPhysicalAddress (cleanSwAddress state immediate rs1)).toNat + 3) =
      some ((cleanSwValue state rs2).extractLsb' 24 8) := by
  exact sailWriteWordState_byte3 sail _ _

theorem sailSwPost_outside (sail : SailState) (state : RV32I.State)
    (immediate : BitVec 12) (rs2 rs1 : RV32I.Register) (observed : Nat)
    (h0 : observed ≠
      (sailPhysicalAddress (cleanSwAddress state immediate rs1)).toNat)
    (h1 : observed ≠
      (sailPhysicalAddress (cleanSwAddress state immediate rs1)).toNat + 1)
    (h2 : observed ≠
      (sailPhysicalAddress (cleanSwAddress state immediate rs1)).toNat + 2)
    (h3 : observed ≠
      (sailPhysicalAddress (cleanSwAddress state immediate rs1)).toNat + 3) :
    (sailSwPost sail state immediate rs2 rs1).mem.get? observed =
      sail.mem.get? observed := by
  exact sailWriteWordState_outside sail _ _ observed h0 h1 h2 h3

theorem cleanSwPost_pc (state : RV32I.State) :
    (cleanSwPost state).pc = state.pc + 4 := by
  rfl

/-- Store callbacks in the reviewed generated profile are configuration-level
no-ops, so they introduce neither hidden state changes nor extra premises. -/
theorem generated_memory_write_callback_noop (name : String)
    (address : LeanRV32D.physaddrbits) (width : Nat)
    (value : BitVec (8 * width)) :
    mem_write_callback name address width value = () := rfl

theorem generated_write_ram_meta_noop (address : LeanRV32D.physaddrbits)
    (width : Nat) :
    LeanRV32D.Functions.__WriteRAM_Meta address width () = () := rfl

theorem clean_execute_sw (state : RV32I.State) (immediate : BitVec 12)
    (rs2 rs1 : RV32I.Register) :
    RV32I.execute (.sw rs2 rs1 immediate) state =
      .request
        (.memory (.store (cleanSwAddress state immediate rs1) .word
          (cleanSwValue state rs2)))
        (RV32I.finishStore state (cleanSwAddress state immediate rs1)
          .word (cleanSwValue state rs2)) := by
  rfl

theorem clean_finishStore_success (state : RV32I.State)
    (address : RV32I.Address) (value : RV32I.Word) :
    RV32I.finishStore state address .word value (.success ()) =
      .done (.retired (cleanSwPost state)) := by
  rfl

/-- A successful clean EEI store response records exactly one completed word
store effect and retires with registers unchanged and PC advanced. -/
theorem clean_sw_success_runs {environmentState : Type}
    (environment : RV32I.ExecutionEnvironment environmentState)
    {before after : environmentState} (state : RV32I.State)
    (immediate : BitVec 12) (rs2 rs1 : RV32I.Register)
    (responds : environment.responds before
      (.memory (.store (cleanSwAddress state immediate rs1) .word
        (cleanSwValue state rs2))) (.success ()) after) :
    RV32I.Interaction.Runs environment
      (RV32I.execute (.sw rs2 rs1 immediate) state) before
      [.memoryAccess
        { request := .store (cleanSwAddress state immediate rs1) .word
            (cleanSwValue state rs2)
          response := .success () }]
      (.retired (cleanSwPost state)) after := by
  rw [clean_execute_sw]
  exact RV32I.Interaction.Runs.request before after after
    (.memory (.store (cleanSwAddress state immediate rs1) .word
      (cleanSwValue state rs2))) (.success ())
    (RV32I.finishStore state (cleanSwAddress state immediate rs1)
      .word (cleanSwValue state rs2)) [] (.retired (cleanSwPost state)) responds
    (RV32I.Interaction.Runs.done after
      (RV32I.InstructionResult.retired (cleanSwPost state)))

/-- Explicit state-level certificate for successful aligned ordinary-RAM SW.
The memory fields expose both the whole-map relation and its exact four-byte
consequences. -/
structure DecodedSwSimulation {environmentState : Type}
    (environment : RV32I.ExecutionEnvironment environmentState)
    (before after : environmentState) (state : RV32I.State)
    (sail : SailState) (immediate : BitVec 12)
    (rs2 rs1 : RV32I.Register) : Prop where
  aligned : RV32I.AccessWidth.word.Aligned
    (cleanSwAddress state immediate rs1)
  effectiveAddress : cleanSwAddress state immediate rs1 =
    state.readRegister rs1 + sign_extend immediate
  sourceValue : cleanSwValue state rs2 = state.readRegister rs2
  generatedSourceRead :
    rX_bits (sailRegister rs2) (sailSequentialStaged sail state) =
      .ok (cleanSwValue state rs2) (sailSequentialStaged sail state)
  requestCorrespondence : DataRequestCorresponds
    (.store (cleanSwAddress state immediate rs1) .word
      (cleanSwValue state rs2))
    (.write .word (sailWriteRequest (cleanSwAddress state immediate rs1)
      .word (cleanSwValue state rs2)))
  cleanExecution : RV32I.execute (.sw rs2 rs1 immediate) state =
    .request
      (.memory (.store (cleanSwAddress state immediate rs1) .word
        (cleanSwValue state rs2)))
      (RV32I.finishStore state (cleanSwAddress state immediate rs1)
        .word (cleanSwValue state rs2))
  cleanRun : RV32I.Interaction.Runs environment
    (RV32I.execute (.sw rs2 rs1 immediate) state) before
    [.memoryAccess
      { request := .store (cleanSwAddress state immediate rs1) .word
          (cleanSwValue state rs2)
        response := .success () }]
    (.retired (cleanSwPost state)) after
  sailExecution : sailDecodedSwStep immediate rs2 rs1 sail =
    .ok (.Retire_Success ()) (sailSwPost sail state immediate rs2 rs1)
  postCorrespondence : StateCorresponds (cleanSwPost state)
    (sailSwPost sail state immediate rs2 rs1)
  registers : ∀ r : RV32I.Register,
    sailReadX (sailSwPost sail state immediate rs2 rs1) r = sailReadX sail r
  x0 : sailReadX (sailSwPost sail state immediate rs2 rs1) 0 = some 0
  pc : (sailSwPost sail state immediate rs2 rs1).regs.get?
    LeanRV32D.Register.PC = some (state.pc + 4)
  memory : StoreMemoryCorresponds sail
    (sailSwPost sail state immediate rs2 rs1)
    (cleanSwAddress state immediate rs1) (cleanSwValue state rs2)
  byte0 : (sailSwPost sail state immediate rs2 rs1).mem.get?
      (sailPhysicalAddress (cleanSwAddress state immediate rs1)).toNat =
    some ((cleanSwValue state rs2).extractLsb' 0 8)
  byte1 : (sailSwPost sail state immediate rs2 rs1).mem.get?
      ((sailPhysicalAddress (cleanSwAddress state immediate rs1)).toNat + 1) =
    some ((cleanSwValue state rs2).extractLsb' 8 8)
  byte2 : (sailSwPost sail state immediate rs2 rs1).mem.get?
      ((sailPhysicalAddress (cleanSwAddress state immediate rs1)).toNat + 2) =
    some ((cleanSwValue state rs2).extractLsb' 16 8)
  byte3 : (sailSwPost sail state immediate rs2 rs1).mem.get?
      ((sailPhysicalAddress (cleanSwAddress state immediate rs1)).toNat + 3) =
    some ((cleanSwValue state rs2).extractLsb' 24 8)
  outside : ∀ observed : Nat,
    observed ≠
        (sailPhysicalAddress (cleanSwAddress state immediate rs1)).toNat →
    observed ≠
        (sailPhysicalAddress (cleanSwAddress state immediate rs1)).toNat + 1 →
    observed ≠
        (sailPhysicalAddress (cleanSwAddress state immediate rs1)).toNat + 2 →
    observed ≠
        (sailPhysicalAddress (cleanSwAddress state immediate rs1)).toNat + 3 →
    (sailSwPost sail state immediate rs2 rs1).mem.get? observed =
      sail.mem.get? observed

/-- Main decoded-SW simulation theorem for a naturally aligned, successful
ordinary-memory word write in the selected Bare profile. -/
theorem decoded_sw_state_simulation {environmentState : Type}
    (environment : RV32I.ExecutionEnvironment environmentState)
    {before after : environmentState} {state : RV32I.State}
    {sail : SailState} (corresponds : StateCorresponds state sail)
    (immediate : BitVec 12) (rs2 rs1 : RV32I.Register)
    (aligned : RV32I.AccessWidth.word.Aligned
      (cleanSwAddress state immediate rs1))
    (path : GeneratedOrdinarySwPath sail state immediate rs2 rs1)
    (responds : environment.responds before
      (.memory (.store (cleanSwAddress state immediate rs1) .word
        (cleanSwValue state rs2))) (.success ()) after) :
    DecodedSwSimulation environment before after state sail immediate
      rs2 rs1 where
  aligned := aligned
  effectiveAddress := sw_effective_address_eq_sail state immediate rs1
  sourceValue := sw_source_value_eq_sail state rs2
  generatedSourceRead := sw_staged_source_read corresponds rs2
  requestCorrespondence := sw_request_corresponds state immediate rs2 rs1
  cleanExecution := clean_execute_sw state immediate rs2 rs1
  cleanRun := clean_sw_success_runs environment state immediate rs2 rs1 responds
  sailExecution := sailDecodedSwStep_success corresponds immediate rs2 rs1 path
  postCorrespondence := sailSwPost_corresponds corresponds immediate rs2 rs1
  registers := sailSwPost_register state sail corresponds immediate rs2 rs1
  x0 := sailSwPost_x0 state sail corresponds immediate rs2 rs1
  pc := sailSwPost_pc_plus_four corresponds immediate rs2 rs1
  memory := sailSwPost_memory_corresponds sail state immediate rs2 rs1
  byte0 := sailSwPost_byte0 sail state immediate rs2 rs1
  byte1 := sailSwPost_byte1 sail state immediate rs2 rs1
  byte2 := sailSwPost_byte2 sail state immediate rs2 rs1
  byte3 := sailSwPost_byte3 sail state immediate rs2 rs1
  outside := sailSwPost_outside sail state immediate rs2 rs1

/-! ## All RV32I base loads and stores

The word-specific theorems above discharge the ordinary Bare RAM path down to
the generated byte backend.  This section factors the instruction-level
argument over all five base loads and all three base stores.  Its path
certificates are deliberately equations at generated `vmem_read` and
`vmem_write`: they expose exactly the platform/privilege route which a bridge
client must review, without importing any generated type into the public
model.  One clean request remains one architectural access; this layer does
not identify that request with every component byte access generated below
Sail's virtual-memory boundary.
-/

/-- The five legal RV32I base-integer load forms.  Keeping this finite type
excludes the nonexistent RV32 `LWU` combination admitted by an unconstrained
width/signedness pair. -/
inductive BaseLoadOperation where
  | lb | lh | lw | lbu | lhu
  deriving DecidableEq, Repr

namespace BaseLoadOperation

def width : BaseLoadOperation → RV32I.AccessWidth
  | .lb | .lbu => .byte
  | .lh | .lhu => .half
  | .lw => .word

def unsigned : BaseLoadOperation → Bool
  | .lbu | .lhu => true
  | .lb | .lh | .lw => false

def instruction (operation : BaseLoadOperation) (rd rs1 : RV32I.Register)
    (immediate : BitVec 12) : RV32I.DecodedInstruction :=
  match operation with
  | .lb => .lb rd rs1 immediate
  | .lh => .lh rd rs1 immediate
  | .lw => .lw rd rs1 immediate
  | .lbu => .lbu rd rs1 immediate
  | .lhu => .lhu rd rs1 immediate

end BaseLoadOperation

/-- The three legal RV32I base-integer store forms. -/
inductive BaseStoreOperation where
  | sb | sh | sw
  deriving DecidableEq, Repr

namespace BaseStoreOperation

def width : BaseStoreOperation → RV32I.AccessWidth
  | .sb => .byte
  | .sh => .half
  | .sw => .word

def instruction (operation : BaseStoreOperation) (rs2 rs1 : RV32I.Register)
    (immediate : BitVec 12) : RV32I.DecodedInstruction :=
  match operation with
  | .sb => .sb rs2 rs1 immediate
  | .sh => .sh rs2 rs1 immediate
  | .sw => .sw rs2 rs1 immediate

end BaseStoreOperation

/-- Generated `extend_value` and the clean load-result operation agree for
every architectural width and signedness.  The operation enumeration below
restricts uses to the five encodable RV32I combinations. -/
theorem extend_value_eq_loadResult_width (width : RV32I.AccessWidth)
    (unsigned : Bool) (value : RV32I.AccessValue width) :
    LeanRV32D.Functions.extend_value unsigned (toSailAccessValue width value) =
      RV32I.Instruction.loadResult width unsigned value := by
  cases width <;> cases unsigned
  case byte.false | half.false =>
    change LeanRV32D.Functions.extend_value false value = value.signExtend 32
    simp [LeanRV32D.Functions.extend_value, sign_extend,
      Sail.BitVec.signExtend]
  case byte.true | half.true => rfl
  case word.false =>
    change LeanRV32D.Functions.extend_value false value = value
    rw [LeanRV32D.Functions.extend_value]
    simp only [Bool.false_eq_true, ↓reduceIte, sign_extend,
      Sail.BitVec.signExtend]
    exact BitVec.signExtend_eq value
  case word.true =>
    change LeanRV32D.Functions.extend_value true value = value
    rw [LeanRV32D.Functions.extend_value]
    simp only [↓reduceIte, LeanRV32D.zero_extend, Sail.BitVec.zeroExtend]
    exact BitVec.setWidth_eq value

theorem extend_value_eq_loadResult (operation : BaseLoadOperation)
    (value : RV32I.AccessValue operation.width) :
    LeanRV32D.Functions.extend_value operation.unsigned
        (toSailAccessValue operation.width value) =
      RV32I.Instruction.loadResult operation.width operation.unsigned value :=
  extend_value_eq_loadResult_width operation.width operation.unsigned value

/-- Generated `execute_STORE` selects exactly the same low lanes as the
clean width-indexed store payload. -/
theorem extract_store_value (width : RV32I.AccessWidth) (value : RV32I.Word) :
    Sail.BitVec.extractLsb value ((width.bytes * 8) - 1) 0 =
      toSailAccessValue width (RV32I.Instruction.storeValue width value) := by
  cases width
  case byte =>
    change Sail.BitVec.extractLsb value 7 0 = value.extractLsb' 0 8
    rfl
  case half =>
    change Sail.BitVec.extractLsb value 15 0 = value.extractLsb' 0 16
    rfl
  case word =>
    change Sail.BitVec.extractLsb value 31 0 = value
    apply BitVec.eq_of_toNat_eq
    simp [Sail.BitVec.extractLsb]
    exact value.isLt

/-- Shared effective address for every decoded base load/store. -/
def cleanDataAddress (state : RV32I.State) (immediate : BitVec 12)
    (rs1 : RV32I.Register) : RV32I.Address :=
  RV32I.Instruction.address immediate (state.readRegister rs1)

def cleanLoadPost (state : RV32I.State) (operation : BaseLoadOperation)
    (rd : RV32I.Register) (value : RV32I.AccessValue operation.width) :
    RV32I.State :=
  { state.writeRegister rd
      (RV32I.Instruction.loadResult operation.width operation.unsigned value) with
    pc := RV32I.nextPc state }

def cleanStorePost (state : RV32I.State) : RV32I.State :=
  { state with pc := RV32I.nextPc state }

/-- Reviewable generic ordinary-Bare load route. It retains Sail's generated
source-register read and effective-address addition, then calls the exact
plain physical request action proved in `SailBridge.Memory`. -/
def sailOrdinaryLoadRead (width : RV32I.AccessWidth)
    (rs1 : RV32I.Register) (offset : RV32I.Word) :
    LeanRV32D.SailM
      (Sail.Result (BitVec (8 * width.bytes)) LeanRV32D.ExecutionResult) := do
  let base ← rX_bits (sailRegister rs1)
  let (value, ()) ← sailReadRamAction (base + offset) width
  pure (.Ok value)

/-- Matching reviewable ordinary-Bare store route. -/
def sailOrdinaryStoreWrite (width : RV32I.AccessWidth)
    (rs1 : RV32I.Register) (offset : RV32I.Word)
    (value : RV32I.AccessValue width) :
    LeanRV32D.SailM (Sail.Result Bool LeanRV32D.ExecutionResult) := do
  let base ← rX_bits (sailRegister rs1)
  let success ← sailWriteRamAction (base + offset) width value
  pure (.Ok success)

/-- Explicit successful generated-load route at the exact staged state.  The
post-read correspondence fields make any callback-visible state effects part
of the reviewed assumption rather than silently assuming them away. -/
structure GeneratedLoadSuccessPath (sail : SailState) (state : RV32I.State)
    (immediate : BitVec 12) (rs1 : RV32I.Register)
    (operation : BaseLoadOperation)
    (value : RV32I.AccessValue operation.width) where
  afterRead : SailState
  route : LeanRV32D.Functions.vmem_read (sailRegister rs1)
      (sign_extend immediate) operation.width.bytes (.Load .Data)
      false false false (sailSequentialStaged sail state) =
    sailOrdinaryLoadRead operation.width rs1 (sign_extend immediate)
      (sailSequentialStaged sail state)
  result : sailOrdinaryLoadRead operation.width rs1 (sign_extend immediate)
      (sailSequentialStaged sail state) =
    .ok (.Ok (toSailAccessValue operation.width value)) afterRead
  stateCorrespondence : StateCorresponds state afterRead
  nextPc : afterRead.regs.get? LeanRV32D.Register.nextPC =
    some (RV32I.nextPc state)

theorem GeneratedLoadSuccessPath.read {sail : SailState} {state : RV32I.State}
    {immediate : BitVec 12} {rs1 : RV32I.Register}
    {operation : BaseLoadOperation}
    {value : RV32I.AccessValue operation.width}
    (path : GeneratedLoadSuccessPath sail state immediate rs1 operation value) :
    LeanRV32D.Functions.vmem_read (sailRegister rs1)
      (sign_extend immediate) operation.width.bytes (.Load .Data)
      false false false (sailSequentialStaged sail state) =
        .ok (.Ok (toSailAccessValue operation.width value)) path.afterRead := by
  rw [path.route, path.result]

theorem execute_LOAD_of_read_success {sail : SailState} {state : RV32I.State}
    (immediate : BitVec 12) (rs1 rd : RV32I.Register)
    (width : RV32I.AccessWidth) (unsigned : Bool)
    (value : RV32I.AccessValue width) (afterRead : SailState)
    (readResult : LeanRV32D.Functions.vmem_read (sailRegister rs1)
      (sign_extend immediate) width.bytes (.Load .Data) false false false
      (sailSequentialStaged sail state) =
        .ok (.Ok (toSailAccessValue width value)) afterRead) :
    LeanRV32D.Functions.execute_LOAD immediate (sailRegister rs1)
        (sailRegister rd) unsigned width.bytes
        (sailSequentialStaged sail state) =
      .ok (.Retire_Success ())
        (sailWriteX afterRead rd
          (RV32I.Instruction.loadResult width unsigned value)) := by
  have writeResult := wX_bits_sailRegister afterRead rd
    (RV32I.Instruction.loadResult width unsigned value)
  have extension := extend_value_eq_loadResult_width width unsigned value
  cases width <;> cases unsigned <;>
    simp [RV32I.AccessWidth.bytes] at readResult extension writeResult ⊢ <;>
    simp [LeanRV32D.Functions.execute_LOAD, readResult, writeResult, extension,
      LeanRV32D.Functions.RETIRE_SUCCESS, LeanRV32D.assert,
      Sail.ConcurrencyInterfaceV1.PreSail.assert,
      LeanRV32D.Functions.xlen_bytes, bind, EStateM.bind, pure, EStateM.pure]

theorem execute_LOAD_success {sail : SailState} {state : RV32I.State}
    (immediate : BitVec 12) (rs1 rd : RV32I.Register)
    (operation : BaseLoadOperation)
    (value : RV32I.AccessValue operation.width)
    (path : GeneratedLoadSuccessPath sail state immediate rs1 operation value) :
    LeanRV32D.Functions.execute_LOAD immediate (sailRegister rs1)
        (sailRegister rd) operation.unsigned operation.width.bytes
        (sailSequentialStaged sail state) =
      .ok (.Retire_Success ())
        (sailWriteX path.afterRead rd
          (RV32I.Instruction.loadResult operation.width operation.unsigned value)) :=
  execute_LOAD_of_read_success immediate rs1 rd operation.width
    operation.unsigned value path.afterRead path.read

/-- Explicit successful generated-store route.  The equation records the
architectural address, width, and low-lane payload passed to generated Sail. -/
structure GeneratedStoreSuccessPath (sail : SailState) (state : RV32I.State)
    (immediate : BitVec 12) (rs2 rs1 : RV32I.Register)
    (operation : BaseStoreOperation) where
  afterWrite : SailState
  route : LeanRV32D.Functions.vmem_write (sailRegister rs1)
      (sign_extend immediate) operation.width.bytes
      (toSailAccessValue operation.width
        (RV32I.Instruction.storeValue operation.width (state.readRegister rs2)))
      (.Store .Data) false false false (sailSequentialStaged sail state) =
    sailOrdinaryStoreWrite operation.width rs1 (sign_extend immediate)
      (RV32I.Instruction.storeValue operation.width (state.readRegister rs2))
      (sailSequentialStaged sail state)
  result : sailOrdinaryStoreWrite operation.width rs1 (sign_extend immediate)
      (RV32I.Instruction.storeValue operation.width (state.readRegister rs2))
      (sailSequentialStaged sail state) =
    .ok (.Ok true) afterWrite
  stateCorrespondence : StateCorresponds state afterWrite
  nextPc : afterWrite.regs.get? LeanRV32D.Register.nextPC =
    some (RV32I.nextPc state)

theorem GeneratedStoreSuccessPath.write {sail : SailState} {state : RV32I.State}
    {immediate : BitVec 12} {rs2 rs1 : RV32I.Register}
    {operation : BaseStoreOperation}
    (path : GeneratedStoreSuccessPath sail state immediate rs2 rs1 operation) :
    LeanRV32D.Functions.vmem_write (sailRegister rs1)
      (sign_extend immediate) operation.width.bytes
      (toSailAccessValue operation.width
        (RV32I.Instruction.storeValue operation.width (state.readRegister rs2)))
      (.Store .Data) false false false (sailSequentialStaged sail state) =
        .ok (.Ok true) path.afterWrite := by
  rw [path.route, path.result]

theorem execute_STORE_of_write_success {sail : SailState} {state : RV32I.State}
    (corresponds : StateCorresponds state sail)
    (immediate : BitVec 12) (rs2 rs1 : RV32I.Register)
    (width : RV32I.AccessWidth) (afterWrite : SailState)
    (writeResult : LeanRV32D.Functions.vmem_write (sailRegister rs1)
      (sign_extend immediate) width.bytes
      (toSailAccessValue width
        (RV32I.Instruction.storeValue width (state.readRegister rs2)))
      (.Store .Data) false false false (sailSequentialStaged sail state) =
        .ok (.Ok true) afterWrite) :
    LeanRV32D.Functions.execute_STORE immediate (sailRegister rs2)
        (sailRegister rs1) width.bytes
        (sailSequentialStaged sail state) =
      .ok (.Retire_Success ()) afterWrite := by
  have readSource := sw_staged_source_read corresponds rs2
  have extracted := extract_store_value width (state.readRegister rs2)
  cases width <;>
    simp [RV32I.AccessWidth.bytes] at extracted writeResult ⊢ <;>
    simp [LeanRV32D.Functions.execute_STORE, cleanSwValue,
      readSource, extracted, writeResult,
      LeanRV32D.Functions.RETIRE_SUCCESS, LeanRV32D.assert,
      Sail.ConcurrencyInterfaceV1.PreSail.assert,
      LeanRV32D.Functions.xlen_bytes, bind, EStateM.bind, pure, EStateM.pure]

theorem execute_STORE_success {sail : SailState} {state : RV32I.State}
    (corresponds : StateCorresponds state sail)
    (immediate : BitVec 12) (rs2 rs1 : RV32I.Register)
    (operation : BaseStoreOperation)
    (path : GeneratedStoreSuccessPath sail state immediate rs2 rs1 operation) :
    LeanRV32D.Functions.execute_STORE immediate (sailRegister rs2)
        (sailRegister rs1) operation.width.bytes
        (sailSequentialStaged sail state) =
      .ok (.Retire_Success ()) path.afterWrite :=
  execute_STORE_of_write_success corresponds immediate rs2 rs1 operation.width
    path.afterWrite path.write

/-! ## RV32I control transfer

The generated model supports optional compressed and landing-pad extensions.
The clean library is specifically RV32I (IALIGN=32), so control-flow bridge
theorems state the relevant generated configuration explicitly rather than
letting those extensions leak into the public semantics. -/

/-- Generated-state assumptions selecting the base RV32I control-flow path.
They are stated at the executor's pre-state because `currentlyEnabled` is a
generated stateful query. Privilege is retained only to identify Sail's trap
result; it is not added to clean unprivileged state. -/
structure BaseControlProfile (sail : SailState) where
  zcaDisabled : currentlyEnabled LeanRV32D.extension.Ext_Zca sail =
    .ok false sail
  zicfilpDisabled : currentlyEnabled LeanRV32D.extension.Ext_Zicfilp sail =
    .ok false sail
  privilege : LeanRV32D.Privilege
  privilegeRead : LeanRV32D.readReg LeanRV32D.Register.cur_privilege sail =
    .ok privilege sail

private theorem sailME_lift_run {α ε : Type}
    (action : LeanRV32D.SailM α) (sail : SailState) :
    (MonadLift.monadLift action : LeanRV32D.SailME ε α) sail =
      match action sail with
      | .ok value after => .ok (.ok value) after
      | .error error after => .error error after := by
  change ExceptT.run (ExceptT.lift action) sail = _
  cases h : action sail <;>
    simp [ExceptT.lift, Functor.map, EStateM.map, h]

private theorem sailME_run_of_ok {α : Type}
    (action : LeanRV32D.SailME α α) (sail after : SailState) (value : α)
    (runs : ExceptT.run action sail = .ok (.ok value) after) :
    LeanRV32D.SailME.run action sail = .ok value after := by
  simp [LeanRV32D.SailME.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, runs,
    bind, EStateM.bind, pure, EStateM.pure]

/-- Direct reduction of generated `jump_to` on the base-RV32I aligned path.
The bit premises expose the generated alignment test explicitly; later path
constructors connect them to the clean `% 4` classification. -/
theorem jump_to_aligned (sail : SailState)
    (profile : BaseControlProfile sail) (target : RV32I.Address)
    (bit0 : Sail.BitVec.access target 0 = 0#1)
    (bit1 : Sail.BitVec.access target 1 = 0#1) :
    jump_to target sail = .ok (.Retire_Success ())
      (sailSetReg sail LeanRV32D.Register.nextPC target) := by
  unfold jump_to
  apply sailME_run_of_ok
  simp only [ext_control_check_pc, bit0, bit1]
  dsimp [liftM, monadLift, instMonadLiftTOfMonadLift, instMonadLiftT]
  simp [sailME_lift_run, ExceptT.run, ExceptT.mk,
    ExceptT.pure, ExceptT.bind, ExceptT.bindCont,
    profile.zcaDisabled, bool_bit_backwards, bit_to_bool,
    LeanRV32D.Functions.not,
    Sail.ConcurrencyInterfaceV1.PreSail.assert, set_next_pc,
    LeanRV32D.writeReg, Sail.ConcurrencyInterfaceV1.PreSail.writeReg,
    redirect_callback, RETIRE_SUCCESS, sailSetReg,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    bind, EStateM.bind, pure, EStateM.pure]

/-- Direct reduction of generated `jump_to` on the IALIGN=32 fault path.
The generated trap retains the attempted target and the faulting PC, while
leaving the sequential state unchanged. -/
theorem jump_to_misaligned {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail)
    (profile : BaseControlProfile sail) (target : RV32I.Address)
    (bit0 : Sail.BitVec.access target 0 = 0#1)
    (bit1 : Sail.BitVec.access target 1 = 1#1) :
    jump_to target sail = .ok (.Trap (profile.privilege,
      make_sync_exception (.E_Fetch_Addr_Align ()) target, state.pc)) sail := by
  have pcRead := readReg_of_get corresponds.pc
  unfold jump_to
  apply sailME_run_of_ok
  simp only [ext_control_check_pc, bit0, bit1]
  dsimp [liftM, monadLift, instMonadLiftTOfMonadLift, instMonadLiftT]
  simp [sailME_lift_run, ExceptT.run, ExceptT.mk,
    ExceptT.bind, ExceptT.bindCont,
    profile.zcaDisabled, bool_bit_backwards, bit_to_bool,
    LeanRV32D.Functions.not,
    Sail.ConcurrencyInterfaceV1.PreSail.assert, memory_exception, trap,
    bits_of_virtaddr, profile.privilegeRead, pcRead,
    bind, EStateM.bind, pure, EStateM.pure]

def cleanBranchInstruction (op : LeanRV32D.bop) (rs1 rs2 : RV32I.Register)
    (immediate : BitVec 13) : RV32I.DecodedInstruction :=
  match op with
  | .BEQ => .beq rs1 rs2 immediate
  | .BNE => .bne rs1 rs2 immediate
  | .BLT => .blt rs1 rs2 immediate
  | .BGE => .bge rs1 rs2 immediate
  | .BLTU => .bltu rs1 rs2 immediate
  | .BGEU => .bgeu rs1 rs2 immediate

def cleanBranchTaken (op : LeanRV32D.bop)
    (rs2Value rs1Value : RV32I.Word) : Bool :=
  match op with
  | .BEQ => RV32I.Instruction.beq rs2Value rs1Value
  | .BNE => RV32I.Instruction.bne rs2Value rs1Value
  | .BLT => RV32I.Instruction.blt rs2Value rs1Value
  | .BGE => RV32I.Instruction.bge rs2Value rs1Value
  | .BLTU => RV32I.Instruction.bltu rs2Value rs1Value
  | .BGEU => RV32I.Instruction.bgeu rs2Value rs1Value

/-- The actual generated BTYPE executor makes exactly the clean branch
decision and delegates only a taken transfer to generated `jump_to`. -/
theorem execute_BTYPE_of_corresponds {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (op : LeanRV32D.bop)
    (immediate : BitVec 13) (rs2 rs1 : RV32I.Register) :
    execute_BTYPE immediate (sailRegister rs2) (sailRegister rs1) op sail =
      if cleanBranchTaken op (state.readRegister rs2) (state.readRegister rs1)
      then jump_to (RV32I.Instruction.pcRelativeTarget immediate state.pc) sail
      else .ok (.Retire_Success ()) sail := by
  have read1 := rX_bits_of_corresponds corresponds rs1
  have read2 := rX_bits_of_corresponds corresponds rs2
  have readPc := readReg_of_get corresponds.pc
  cases op <;>
    simp only [execute_BTYPE, bind, EStateM.bind, pure, EStateM.pure,
      read1, read2, readPc] <;>
    simp [cleanBranchTaken, RV32I.Instruction.beq,
      RV32I.Instruction.bne, RV32I.Instruction.blt, RV32I.Instruction.bge,
      RV32I.Instruction.bltu, RV32I.Instruction.bgeu,
      RV32I.Instruction.pcRelativeTarget, sign_extend,
      Sail.BitVec.signExtend, zopz0zI_s, zopz0zI_u, BitVec.slt, BitVec.ult,
      zopz0zKzJ_s, zopz0zKzJ_u, Sail.BitVec.toNatInt,
      read1, read2, readPc] <;>
    split <;> simp_all [bind, EStateM.bind, pure, EStateM.pure, RETIRE_SUCCESS]

theorem clean_execute_branch (state : RV32I.State) (op : LeanRV32D.bop)
    (immediate : BitVec 13) (rs2 rs1 : RV32I.Register) :
    RV32I.execute (cleanBranchInstruction op rs1 rs2 immediate) state =
      RV32I.executeBranch state
        (cleanBranchTaken op (state.readRegister rs2) (state.readRegister rs1))
        immediate := by
  cases op <;> rfl

/-- Auditable boundary around generated `jump_to`, analogous to the existing
generated virtual-memory path witnesses. It records the selected base profile,
the IALIGN=32 classification, the actual generated call, and its exact result.
The misaligned case requires the generated trap to retain the attempted target
as exception information and leave sequential state unchanged. -/
inductive GeneratedJumpPath (state : RV32I.State) (sail : SailState)
    (profile : BaseControlProfile sail) (target : RV32I.Address) : Type where
  | aligned (proof : target.toNat % 4 = 0) :
      (after : SailState) →
      jump_to target sail = .ok (.Retire_Success ()) after →
      after.regs.get? LeanRV32D.Register.nextPC = some target →
      (∀ r : RV32I.Register, sailReadX after r = sailReadX sail r) →
      after.regs.get? LeanRV32D.Register.PC = some state.pc →
      GeneratedJumpPath state sail profile target
  | misaligned (proof : target.toNat % 4 ≠ 0) :
      jump_to target sail =
        .ok (.Trap (profile.privilege,
          make_sync_exception (.E_Fetch_Addr_Align ()) target, state.pc)) sail →
      GeneratedJumpPath state sail profile target

/-- Construct the aligned generated path from the reviewed base profile and
the generated function's two low-bit tests. -/
def generatedJumpPath_aligned {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail)
    (profile : BaseControlProfile sail) (target : RV32I.Address)
    (aligned : target.toNat % 4 = 0)
    (bit0 : Sail.BitVec.access target 0 = 0#1)
    (bit1 : Sail.BitVec.access target 1 = 0#1) :
    GeneratedJumpPath state sail profile target :=
  .aligned aligned
    (sailSetReg sail LeanRV32D.Register.nextPC target)
    (jump_to_aligned sail profile target bit0 bit1)
    (by simp [sailSetReg, Std.ExtDHashMap.get?_insert])
    (sailReadX_set_nextPc sail target)
    (by simpa [sailSetReg, Std.ExtDHashMap.get?_insert] using corresponds.pc)

/-- Construct the misaligned generated path, including exact target-bearing
trap information, from the reviewed base profile. -/
def generatedJumpPath_misaligned {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail)
    (profile : BaseControlProfile sail) (target : RV32I.Address)
    (misaligned : target.toNat % 4 ≠ 0)
    (bit0 : Sail.BitVec.access target 0 = 0#1)
    (bit1 : Sail.BitVec.access target 1 = 1#1) :
    GeneratedJumpPath state sail profile target :=
  .misaligned misaligned
    (jump_to_misaligned corresponds profile target bit0 bit1)

/-- The path witness cannot classify one target as both aligned and
misaligned. -/
theorem generatedJumpPath_alignment_exclusive
    {state : RV32I.State} {sail : SailState}
    {profile : BaseControlProfile sail} {target : RV32I.Address}
    (path : GeneratedJumpPath state sail profile target) :
    (target.toNat % 4 = 0) ∨ (target.toNat % 4 ≠ 0) := by
  cases path with
  | aligned proof => exact .inl proof
  | misaligned proof => exact .inr proof

theorem execute_BTYPE_not_taken {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (op : LeanRV32D.bop)
    (immediate : BitVec 13) (rs2 rs1 : RV32I.Register)
    (notTaken : cleanBranchTaken op (state.readRegister rs2)
      (state.readRegister rs1) = false) :
    execute_BTYPE immediate (sailRegister rs2) (sailRegister rs1) op sail =
      .ok (.Retire_Success ()) sail := by
  rw [execute_BTYPE_of_corresponds corresponds]
  simp [notTaken]

theorem execute_BTYPE_taken {state : RV32I.State} {sail : SailState}
    (corresponds : StateCorresponds state sail) (op : LeanRV32D.bop)
    (immediate : BitVec 13) (rs2 rs1 : RV32I.Register)
    (taken : cleanBranchTaken op (state.readRegister rs2)
      (state.readRegister rs1) = true) :
    execute_BTYPE immediate (sailRegister rs2) (sailRegister rs1) op sail =
      jump_to (RV32I.Instruction.pcRelativeTarget immediate state.pc) sail := by
  rw [execute_BTYPE_of_corresponds corresponds]
  simp [taken]

/-- BTYPE validation packages the pure branch-decision proof with the actual
generated `jump_to` path selected for a taken branch. -/
structure DecodedBranchSimulation (state : RV32I.State) (sail : SailState)
    (profile : BaseControlProfile sail) (op : LeanRV32D.bop)
    (immediate : BitVec 13) (rs2 rs1 : RV32I.Register) : Type where
  cleanExecution :
    RV32I.execute (cleanBranchInstruction op rs1 rs2 immediate) state =
      RV32I.executeBranch state
        (cleanBranchTaken op (state.readRegister rs2) (state.readRegister rs1))
        immediate
  generatedDecision :
    execute_BTYPE immediate (sailRegister rs2) (sailRegister rs1) op sail =
      if cleanBranchTaken op (state.readRegister rs2) (state.readRegister rs1)
      then jump_to (RV32I.Instruction.pcRelativeTarget immediate state.pc) sail
      else .ok (.Retire_Success ()) sail
  takenPath : cleanBranchTaken op (state.readRegister rs2)
      (state.readRegister rs1) = true →
    GeneratedJumpPath state sail profile
      (RV32I.Instruction.pcRelativeTarget immediate state.pc)

def decoded_branch_state_simulation {state : RV32I.State}
    {sail : SailState} (corresponds : StateCorresponds state sail)
    (profile : BaseControlProfile sail) (op : LeanRV32D.bop)
    (immediate : BitVec 13) (rs2 rs1 : RV32I.Register)
    (takenPath : cleanBranchTaken op (state.readRegister rs2)
        (state.readRegister rs1) = true →
      GeneratedJumpPath state sail profile
        (RV32I.Instruction.pcRelativeTarget immediate state.pc)) :
    DecodedBranchSimulation state sail profile op immediate rs2 rs1 where
  cleanExecution := clean_execute_branch state op immediate rs2 rs1
  generatedDecision := execute_BTYPE_of_corresponds corresponds op immediate rs2 rs1
  takenPath := takenPath

theorem clean_execute_jal (state : RV32I.State) (immediate : BitVec 21)
    (rd : RV32I.Register) :
    RV32I.execute (.jal rd immediate) state =
      RV32I.finishJump state (state.writeRegister rd (RV32I.nextPc state))
        (RV32I.Instruction.pcRelativeTarget immediate state.pc) := by
  rfl

theorem clean_execute_jalr (state : RV32I.State) (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) :
    RV32I.execute (.jalr rd rs1 immediate) state =
      RV32I.finishJump state (state.writeRegister rd (RV32I.nextPc state))
        (RV32I.Instruction.jalrTarget immediate (state.readRegister rs1)) := by
  rfl

theorem generated_jalr_target_eq_clean (immediate : BitVec 12)
    (base : RV32I.Word) :
    Sail.BitVec.update (base + sign_extend (m := 32) immediate) 0 0#1 =
      RV32I.Instruction.jalrTarget immediate base := by
  simp [Sail.BitVec.update, Sail.BitVec.updateSubrange',
    RV32I.Instruction.jalrTarget, sign_extend, Sail.BitVec.signExtend]
  bv_decide

theorem update_elp_state_base (sail : SailState)
    (profile : BaseControlProfile sail) (rs1 : RV32I.Register) :
    update_elp_state (sailRegister rs1) sail = .ok () sail := by
  simp [update_elp_state, profile.zicfilpDisabled, bind, EStateM.bind,
    pure, EStateM.pure]

/-- If generated `jump_to` accepts JAL's target, the actual JAL executor
writes precisely the staged sequential PC as its link. -/
theorem execute_JAL_success {state : RV32I.State} {sail after : SailState}
    (staged : StagedStateCorresponds state sail) (immediate : BitVec 21)
    (rd : RV32I.Register)
    (jumpRuns : jump_to (RV32I.Instruction.pcRelativeTarget immediate state.pc) sail =
      .ok (.Retire_Success ()) after) :
    execute_JAL immediate (sailRegister rd) sail =
      .ok (.Retire_Success ()) (sailWriteX after rd (RV32I.nextPc state)) := by
  have readLink := readReg_of_get staged.nextPc
  have readPc := readReg_of_get staged.pc
  have writeLink := wX_bits_sailRegister after rd (RV32I.nextPc state)
  change jump_to (state.pc + immediate.signExtend 32) sail =
    .ok (.Retire_Success ()) after at jumpRuns
  simp [execute_JAL, get_next_pc, RV32I.Instruction.pcRelativeTarget,
    sign_extend, Sail.BitVec.signExtend, readLink, readPc, jumpRuns,
    writeLink, bind, EStateM.bind, pure, EStateM.pure]

/-- A generated JAL target failure returns before its link write. -/
theorem execute_JAL_failure {state : RV32I.State} {sail : SailState}
    (staged : StagedStateCorresponds state sail) (profile : BaseControlProfile sail)
    (immediate : BitVec 21) (rd : RV32I.Register)
    (jumpRuns : jump_to (RV32I.Instruction.pcRelativeTarget immediate state.pc) sail =
      .ok (.Trap (profile.privilege,
        make_sync_exception (.E_Fetch_Addr_Align ())
          (RV32I.Instruction.pcRelativeTarget immediate state.pc), state.pc)) sail) :
    execute_JAL immediate (sailRegister rd) sail =
      .ok (.Trap (profile.privilege,
        make_sync_exception (.E_Fetch_Addr_Align ())
          (RV32I.Instruction.pcRelativeTarget immediate state.pc), state.pc)) sail := by
  have readLink := readReg_of_get staged.nextPc
  have readPc := readReg_of_get staged.pc
  change jump_to (state.pc + immediate.signExtend 32) sail =
    .ok (.Trap (profile.privilege,
      make_sync_exception (.E_Fetch_Addr_Align ())
        (state.pc + immediate.signExtend 32), state.pc)) sail at jumpRuns
  simp [execute_JAL, get_next_pc, RV32I.Instruction.pcRelativeTarget,
    sign_extend, Sail.BitVec.signExtend, readLink, readPc, jumpRuns,
    bind, EStateM.bind, pure, EStateM.pure]

/-- The actual JALR executor uses the clean target, including mandatory bit
zero clearing, and writes its link only after generated `jump_to` succeeds. -/
theorem execute_JALR_success {state : RV32I.State} {sail after : SailState}
    (staged : StagedStateCorresponds state sail) (profile : BaseControlProfile sail)
    (immediate : BitVec 12) (rs1 rd : RV32I.Register)
    (jumpRuns : jump_to
        (RV32I.Instruction.jalrTarget immediate (state.readRegister rs1)) sail =
      .ok (.Retire_Success ()) after) :
    execute_JALR immediate (sailRegister rs1) (sailRegister rd) sail =
      .ok (.Retire_Success ()) (sailWriteX after rd (RV32I.nextPc state)) := by
  have elp := update_elp_state_base sail profile rs1
  have readLink := readReg_of_get staged.nextPc
  have readSource : rX_bits (sailRegister rs1) sail =
      .ok (state.readRegister rs1) sail :=
    rX_bits_of_corresponds { pc := staged.pc, register := staged.register } rs1
  have writeLink := wX_bits_sailRegister after rd (RV32I.nextPc state)
  have targetEq := generated_jalr_target_eq_clean immediate
    (state.readRegister rs1)
  simp [execute_JALR, elp, get_next_pc, readLink, readSource,
    targetEq, jumpRuns, writeLink,
    bind, EStateM.bind, pure, EStateM.pure]

theorem execute_JALR_failure {state : RV32I.State} {sail : SailState}
    (staged : StagedStateCorresponds state sail) (profile : BaseControlProfile sail)
    (immediate : BitVec 12) (rs1 rd : RV32I.Register)
    (jumpRuns : jump_to
        (RV32I.Instruction.jalrTarget immediate (state.readRegister rs1)) sail =
      .ok (.Trap (profile.privilege,
        make_sync_exception (.E_Fetch_Addr_Align ())
          (RV32I.Instruction.jalrTarget immediate (state.readRegister rs1)),
          state.pc)) sail) :
    execute_JALR immediate (sailRegister rs1) (sailRegister rd) sail =
      .ok (.Trap (profile.privilege,
        make_sync_exception (.E_Fetch_Addr_Align ())
          (RV32I.Instruction.jalrTarget immediate (state.readRegister rs1)),
          state.pc)) sail := by
  have elp := update_elp_state_base sail profile rs1
  have readLink := readReg_of_get staged.nextPc
  have readSource : rX_bits (sailRegister rs1) sail =
      .ok (state.readRegister rs1) sail :=
    rX_bits_of_corresponds { pc := staged.pc, register := staged.register } rs1
  have targetEq := generated_jalr_target_eq_clean immediate
    (state.readRegister rs1)
  simp [execute_JALR, elp, get_next_pc, readLink, readSource,
    targetEq, jumpRuns,
    bind, EStateM.bind, pure, EStateM.pure]

/-- Correspondence at the generated control-transfer staging point: Sail still
holds the faulting PC in `PC`, has the accepted successor in `nextPC`, and its
integer registers agree with the clean retired successor. -/
structure ControlTransferStagedCorresponds (next : RV32I.State)
    (oldPc : RV32I.Address) (sail : SailState) : Prop where
  pc : sail.regs.get? LeanRV32D.Register.PC = some oldPc
  nextPc : sail.regs.get? LeanRV32D.Register.nextPC = some next.pc
  register : ∀ r : RV32I.Register,
    sailReadX sail r = some (next.readRegister r)

theorem accepted_jump_and_link_corresponds {state : RV32I.State}
    {sail after : SailState} (staged : StagedStateCorresponds state sail)
    (rd : RV32I.Register) (target : RV32I.Address)
    (nextPcSet : after.regs.get? LeanRV32D.Register.nextPC = some target)
    (registersPreserved : ∀ r : RV32I.Register,
      sailReadX after r = sailReadX sail r)
    (pcPreserved : after.regs.get? LeanRV32D.Register.PC = some state.pc) :
    ControlTransferStagedCorresponds
      { state.writeRegister rd (RV32I.nextPc state) with pc := target }
      state.pc (sailWriteX after rd (RV32I.nextPc state)) := by
  have afterCorresponds : StateCorresponds state after :=
    { pc := pcPreserved
      register := fun r => (registersPreserved r).trans (staged.register r) }
  have written := afterCorresponds.writeX rd (RV32I.nextPc state)
  constructor
  · simpa [clean_writeRegister_pc] using written.pc
  · rw [sailWriteX_nextPc]
    exact nextPcSet
  · exact written.register

/-- End-to-end decoded-executor simulation for JAL. On success both models
accept the same target and write the same link; on failure both retain the
pre-instruction state and expose the same misaligned target. -/
inductive DecodedJalSimulation (state : RV32I.State) (sail : SailState)
    (profile : BaseControlProfile sail) (immediate : BitVec 21)
    (rd : RV32I.Register) : Type where
  | aligned
      (targetAligned : (RV32I.Instruction.pcRelativeTarget immediate state.pc).toNat % 4 = 0)
      (after : SailState)
      (cleanExecution : RV32I.execute (.jal rd immediate) state =
        .done (.retired
          { state.writeRegister rd (RV32I.nextPc state) with
            pc := RV32I.Instruction.pcRelativeTarget immediate state.pc }))
      (sailExecution : execute_JAL immediate (sailRegister rd) sail =
        .ok (.Retire_Success ())
          (sailWriteX after rd (RV32I.nextPc state)))
      (postCorrespondence : ControlTransferStagedCorresponds
        { state.writeRegister rd (RV32I.nextPc state) with
          pc := RV32I.Instruction.pcRelativeTarget immediate state.pc }
        state.pc (sailWriteX after rd (RV32I.nextPc state)))
  | misaligned
      (targetMisaligned : (RV32I.Instruction.pcRelativeTarget immediate state.pc).toNat % 4 ≠ 0)
      (cleanExecution : RV32I.execute (.jal rd immediate) state =
        .done (.raised state (.instructionAddressMisaligned
          (RV32I.Instruction.pcRelativeTarget immediate state.pc))))
      (sailExecution : execute_JAL immediate (sailRegister rd) sail =
        .ok (.Trap (profile.privilege,
          make_sync_exception (.E_Fetch_Addr_Align ())
            (RV32I.Instruction.pcRelativeTarget immediate state.pc), state.pc)) sail)

def decoded_jal_state_simulation {state : RV32I.State} {sail : SailState}
    (staged : StagedStateCorresponds state sail)
    (profile : BaseControlProfile sail) (immediate : BitVec 21)
    (rd : RV32I.Register)
    (path : GeneratedJumpPath state sail profile
      (RV32I.Instruction.pcRelativeTarget immediate state.pc)) :
    DecodedJalSimulation state sail profile immediate rd := by
  cases path with
  | aligned proof after jumpRuns nextPcSet registersPreserved pcPreserved =>
      exact .aligned proof after
        (by simp [RV32I.execute, RV32I.finishJump, proof])
        (execute_JAL_success staged immediate rd jumpRuns)
        (accepted_jump_and_link_corresponds staged rd _ nextPcSet
          registersPreserved pcPreserved)
  | misaligned proof jumpRuns =>
      exact .misaligned proof
        (by simp [RV32I.execute, RV32I.finishJump, proof])
        (execute_JAL_failure staged profile immediate rd jumpRuns)

/-- The corresponding JALR simulation additionally validates source-based
target calculation and bit-zero clearing before the same alignment split. -/
inductive DecodedJalrSimulation (state : RV32I.State) (sail : SailState)
    (profile : BaseControlProfile sail) (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) : Type where
  | aligned
      (targetAligned : (RV32I.Instruction.jalrTarget immediate
        (state.readRegister rs1)).toNat % 4 = 0)
      (after : SailState)
      (cleanExecution : RV32I.execute (.jalr rd rs1 immediate) state =
        .done (.retired
          { state.writeRegister rd (RV32I.nextPc state) with
            pc := RV32I.Instruction.jalrTarget immediate
              (state.readRegister rs1) }))
      (sailExecution : execute_JALR immediate (sailRegister rs1)
        (sailRegister rd) sail = .ok (.Retire_Success ())
          (sailWriteX after rd (RV32I.nextPc state)))
      (postCorrespondence : ControlTransferStagedCorresponds
        { state.writeRegister rd (RV32I.nextPc state) with
          pc := RV32I.Instruction.jalrTarget immediate
            (state.readRegister rs1) }
        state.pc (sailWriteX after rd (RV32I.nextPc state)))
  | misaligned
      (targetMisaligned : (RV32I.Instruction.jalrTarget immediate
        (state.readRegister rs1)).toNat % 4 ≠ 0)
      (cleanExecution : RV32I.execute (.jalr rd rs1 immediate) state =
        .done (.raised state (.instructionAddressMisaligned
          (RV32I.Instruction.jalrTarget immediate (state.readRegister rs1)))))
      (sailExecution : execute_JALR immediate (sailRegister rs1)
        (sailRegister rd) sail = .ok (.Trap (profile.privilege,
          make_sync_exception (.E_Fetch_Addr_Align ())
            (RV32I.Instruction.jalrTarget immediate (state.readRegister rs1)),
            state.pc)) sail)

def decoded_jalr_state_simulation {state : RV32I.State} {sail : SailState}
    (staged : StagedStateCorresponds state sail)
    (profile : BaseControlProfile sail) (immediate : BitVec 12)
    (rs1 rd : RV32I.Register)
    (path : GeneratedJumpPath state sail profile
      (RV32I.Instruction.jalrTarget immediate (state.readRegister rs1))) :
    DecodedJalrSimulation state sail profile immediate rs1 rd := by
  cases path with
  | aligned proof after jumpRuns nextPcSet registersPreserved pcPreserved =>
      exact .aligned proof after
        (by simp [RV32I.execute, RV32I.finishJump, proof])
        (execute_JALR_success staged profile immediate rs1 rd jumpRuns)
        (accepted_jump_and_link_corresponds staged rd _ nextPcSet
          registersPreserved pcPreserved)
  | misaligned proof jumpRuns =>
      exact .misaligned proof
        (by simp [RV32I.execute, RV32I.finishJump, proof])
        (execute_JALR_failure staged profile immediate rs1 rd jumpRuns)

end RV32I.SailBridge
