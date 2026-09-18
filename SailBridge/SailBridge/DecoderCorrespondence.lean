import RV32ISailBridge

/-!
Bridge-only vocabulary for comparing the clean base-RV32I decoder with Sail's
generated instruction datatype.  This file deliberately does not make the
generated decoder part of the public `RV32I` library.
-/

namespace RV32I.SailBridge

open LeanRV32D.Functions

/-- The only generated-state condition needed to prevent an optional
extension from changing the meaning of a clean-legal base word.  Zihintntl and
Zihintpause are not listed: this generated platform hard-enables them, and the
base view below deliberately recognizes their compatible HINT refinements. -/
structure BaseDecoderProfile (sail : SailState) where
  zicfilpDisabled : currentlyEnabled .Ext_Zicfilp sail = .ok false sail

theorem zihintntl_enabled (sail : SailState) :
    currentlyEnabled .Ext_Zihintntl sail = .ok true sail := by
  simp [currentlyEnabled, hartSupports, pure, EStateM.pure]

theorem zihintpause_enabled (sail : SailState) :
    currentlyEnabled .Ext_Zihintpause sail = .ok true sail := by
  simp [currentlyEnabled, hartSupports, pure, EStateM.pure]

/-! Small round trips for the generated operand mappings.  These are the
factored leaves used by decoder-family proofs; no theorem below unfolds the
monolithic instruction mapping. -/

@[simp] theorem encdec_uop_roundtrip (operation : LeanRV32D.uop)
    (sail : SailState) :
    encdec_uop_backwards (encdec_uop_forwards operation) sail =
      .ok operation sail := by
  cases operation <;> rfl

@[simp] theorem encdec_bop_roundtrip (operation : LeanRV32D.bop)
    (sail : SailState) :
    encdec_bop_backwards (encdec_bop_forwards operation) sail =
      .ok operation sail := by
  cases operation <;> rfl

@[simp] theorem encdec_iop_roundtrip (operation : LeanRV32D.iop)
    (sail : SailState) :
    encdec_iop_backwards (encdec_iop_forwards operation) sail =
      .ok operation sail := by
  cases operation <;> rfl

@[simp] theorem encdec_ntl_roundtrip (operation : LeanRV32D.ntl_type)
    (sail : SailState) :
    encdec_ntl_backwards (encdec_ntl_forwards operation) sail =
      .ok operation sail := by
  cases operation <;> rfl

theorem encdec_ntl_matcher_characterization :
    ∀ bits : BitVec 5,
      encdec_ntl_backwards_matches bits = true ↔
        bits = 0b00010#5 ∨ bits = 0b00011#5 ∨
        bits = 0b00100#5 ∨ bits = 0b00101#5 := by
  native_decide

@[simp] theorem encdec_cbop_zicbop_roundtrip
    (operation : LeanRV32D.cbop_zicbop) (sail : SailState) :
    encdec_cbop_zicbop_backwards
        (encdec_cbop_zicbop_forwards operation) sail =
      .ok operation sail := by
  cases operation <;> rfl

theorem encdec_cbop_zicbop_matcher_characterization :
    ∀ bits : BitVec 5,
      encdec_cbop_zicbop_backwards_matches bits = true ↔
        bits = 0b00000#5 ∨ bits = 0b00001#5 ∨ bits = 0b00011#5 := by
  native_decide

@[simp] theorem encdec_slli_roundtrip (sail : SailState) :
    encdec_sop_backwards (encdec_sop_forwards .SLLI) sail =
      .ok .SLLI sail := by
  rfl

@[simp] theorem encdec_srli_roundtrip (sail : SailState) :
    encdec_sop_backwards (encdec_sop_forwards .SRLI) sail =
      .ok .SRLI sail := by
  rfl

/-- The generated `sop` forward mapping is intentionally not injective:
SRAI and SRLI share `funct3=101` and the instruction decoder distinguishes
them using the upper immediate bits.  Accordingly there is no false generic
round-trip theorem for `encdec_sop`. -/
theorem encdec_sop_srai_alias :
    encdec_sop_forwards .SRAI = encdec_sop_forwards .SRLI := by
  rfl

@[simp] theorem encdec_reg_roundtrip (register : LeanRV32D.regidx)
    (sail : SailState) :
    encdec_reg_backwards (encdec_reg_forwards register) sail =
      .ok register sail := by
  rcases register with ⟨bits⟩
  simp [encdec_reg_backwards, encdec_reg_forwards,
    LeanRV32D.Functions.base_E_enabled,
    LeanRV32D.Functions.regidx_bit_width, LeanRV32D.Functions.not,
    pure, EStateM.pure, LeanRV32D.zero_extend, Sail.BitVec.zeroExtend,
    Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem encdec_reg_backwards_matches_rv32 (bits : BitVec 5) :
    encdec_reg_backwards_matches bits = true := by
  simp [encdec_reg_backwards_matches,
    LeanRV32D.Functions.base_E_enabled, LeanRV32D.Functions.not]

@[simp] theorem encdec_reg_forwards_zero :
    encdec_reg_forwards (sailRegister (0 : RV32I.Register)) = 0#5 := by
  rfl

@[simp] theorem encdec_reg_payload_roundtrip (register : LeanRV32D.regidx) :
    LeanRV32D.regidx.Regidx
        (Sail.BitVec.extractLsb (encdec_reg_forwards register)
          (LeanRV32D.Functions.regidx_bit_width -i 1) 0) =
      register := by
  rcases register with ⟨bits⟩
  apply congrArg LeanRV32D.regidx.Regidx
  simp [encdec_reg_forwards, LeanRV32D.Functions.regidx_bit_width,
    LeanRV32D.zero_extend, Sail.BitVec.zeroExtend,
    Sail.BitVec.extractLsb, BitVec.extractLsb]

/-- Recover the architectural register number carried by a generated register
index.  The generated RV32 configuration uses five-bit register indices. -/
def cleanRegister : LeanRV32D.regidx → RV32I.Register
  | .Regidx bits => bits.toFin

@[simp] theorem cleanRegister_sailRegister (register : RV32I.Register) :
    cleanRegister (sailRegister register) = register := by
  apply Fin.ext
  simp [cleanRegister, sailRegister]

/-! The generated U-type encoding is deliberately factored into its three
architectural fields.  These lemmas are small bit-vector facts, independent
of the generated instruction decoder's clause tree. -/

@[simp] theorem generatedUtypeEncoding_immediate (immediate : BitVec 20)
    (rd : RV32I.Register) (operation : LeanRV32D.uop) :
    Sail.BitVec.extractLsb (generatedUtypeEncoding immediate rd operation)
        31 12 = immediate := by
  simp [generatedUtypeEncoding, Sail.BitVec.extractLsb, encdec_reg_forwards,
    sailRegister, LeanRV32D.zero_extend, Sail.BitVec.zeroExtend]
  bv_decide

@[simp] theorem generatedUtypeEncoding_rd (immediate : BitVec 20)
    (rd : RV32I.Register) (operation : LeanRV32D.uop) :
    Sail.BitVec.extractLsb (generatedUtypeEncoding immediate rd operation)
        11 7 = encdec_reg_forwards (sailRegister rd) := by
  simp [generatedUtypeEncoding, Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedUtypeEncoding_opcode (immediate : BitVec 20)
    (rd : RV32I.Register) (operation : LeanRV32D.uop) :
    Sail.BitVec.extractLsb (generatedUtypeEncoding immediate rd operation)
        6 0 = encdec_uop_forwards operation := by
  simp [generatedUtypeEncoding, Sail.BitVec.extractLsb]
  bv_decide

/-! JAL is parameterized by the twenty stored immediate bits.  Appending its
implicit zero bit gives the architectural 21-bit displacement.  This
parameterization covers every raw JAL word without imposing an extra
well-formedness premise. -/

def generatedJalEncoding (storedImmediate : BitVec 20)
    (rd : RV32I.Register) : RV32I.Word :=
  storedImmediate.extractLsb' 19 1 ++
    storedImmediate.extractLsb' 0 10 ++
    storedImmediate.extractLsb' 10 1 ++
    storedImmediate.extractLsb' 11 8 ++
    encdec_reg_forwards (sailRegister rd) ++ 0b1101111#7

@[simp] theorem generatedJalEncoding_bit31 (immediate : BitVec 20)
    (rd : RV32I.Register) :
    Sail.BitVec.extractLsb (generatedJalEncoding immediate rd) 31 31 =
      immediate.extractLsb' 19 1 := by
  simp [generatedJalEncoding, Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedJalEncoding_bits30_21 (immediate : BitVec 20)
    (rd : RV32I.Register) :
    Sail.BitVec.extractLsb (generatedJalEncoding immediate rd) 30 21 =
      immediate.extractLsb' 0 10 := by
  simp [generatedJalEncoding, Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedJalEncoding_bit20 (immediate : BitVec 20)
    (rd : RV32I.Register) :
    Sail.BitVec.extractLsb (generatedJalEncoding immediate rd) 20 20 =
      immediate.extractLsb' 10 1 := by
  simp [generatedJalEncoding, Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedJalEncoding_bits19_12 (immediate : BitVec 20)
    (rd : RV32I.Register) :
    Sail.BitVec.extractLsb (generatedJalEncoding immediate rd) 19 12 =
      immediate.extractLsb' 11 8 := by
  simp [generatedJalEncoding, Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedJalEncoding_rd (immediate : BitVec 20)
    (rd : RV32I.Register) :
    Sail.BitVec.extractLsb (generatedJalEncoding immediate rd) 11 7 =
      encdec_reg_forwards (sailRegister rd) := by
  simp [generatedJalEncoding, Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedJalEncoding_opcode (immediate : BitVec 20)
    (rd : RV32I.Register) :
    Sail.BitVec.extractLsb (generatedJalEncoding immediate rd) 6 0 =
      0b1101111#7 := by
  simp [generatedJalEncoding, Sail.BitVec.extractLsb]
  bv_decide

/-- Reassembling Sail's four stored JAL fields and low zero bit recovers the
architectural 21-bit immediate. -/
@[simp] theorem generatedJalImmediate_roundtrip (immediate : BitVec 20) :
    (((immediate.extractLsb' 19 1 +++ immediate.extractLsb' 11 8) +++
        immediate.extractLsb' 10 1) +++ immediate.extractLsb' 0 10) +++ 0#1 =
      immediate +++ 0#1 := by
  bv_decide

@[simp] theorem clean_decodes_generatedJalEncoding (immediate : BitVec 20)
    (rd : RV32I.Register) :
    RV32I.Decoder.decode (generatedJalEncoding immediate rd) =
      some (.jal rd (immediate ++ 0#1)) := by
  have hopcode : RV32I.Decoder.opcode
      (generatedJalEncoding immediate rd) = 0b1101111#7 := by
    simp [RV32I.Decoder.opcode, generatedJalEncoding]
    bv_decide
  have hrd : RV32I.Decoder.rd (generatedJalEncoding immediate rd) = rd := by
    clear hopcode
    have bits : (generatedJalEncoding immediate rd).extractLsb' 7 5 =
        BitVec.ofNat 5 rd.val := by
      simp [generatedJalEncoding, encdec_reg_forwards, sailRegister,
        LeanRV32D.zero_extend, Sail.BitVec.zeroExtend]
      bv_decide
    simp [RV32I.Decoder.rd, bits]
  have himmediate : RV32I.Decoder.jImmediate
      (generatedJalEncoding immediate rd) = immediate ++ 0#1 := by
    clear hopcode hrd
    simp [RV32I.Decoder.jImmediate, generatedJalEncoding]
    bv_decide
  simp [RV32I.Decoder.decode, hopcode, hrd, himmediate]

/-! JALR has the ordinary I-type layout with a fixed zero `funct3`. -/

def generatedJalrEncoding (immediate : BitVec 12) (rs1 rd : RV32I.Register) :
    RV32I.Word :=
  immediate +++ encdec_reg_forwards (sailRegister rs1) +++ 0b000#3 +++
    encdec_reg_forwards (sailRegister rd) +++ 0b1100111#7

@[simp] theorem generatedJalrEncoding_immediate (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) :
    Sail.BitVec.extractLsb (generatedJalrEncoding immediate rs1 rd) 31 20 =
      immediate := by
  simp [generatedJalrEncoding, Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedJalrEncoding_rs1 (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) :
    Sail.BitVec.extractLsb (generatedJalrEncoding immediate rs1 rd) 19 15 =
      encdec_reg_forwards (sailRegister rs1) := by
  simp [generatedJalrEncoding, Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedJalrEncoding_funct3 (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) :
    Sail.BitVec.extractLsb (generatedJalrEncoding immediate rs1 rd) 14 12 =
      0b000#3 := by
  simp [generatedJalrEncoding, Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedJalrEncoding_rd (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) :
    Sail.BitVec.extractLsb (generatedJalrEncoding immediate rs1 rd) 11 7 =
      encdec_reg_forwards (sailRegister rd) := by
  simp [generatedJalrEncoding, Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedJalrEncoding_opcode (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) :
    Sail.BitVec.extractLsb (generatedJalrEncoding immediate rs1 rd) 6 0 =
      0b1100111#7 := by
  simp [generatedJalrEncoding, Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem clean_decodes_generatedJalrEncoding (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) :
    RV32I.Decoder.decode (generatedJalrEncoding immediate rs1 rd) =
      some (.jalr rd rs1 immediate) := by
  have hopcode : RV32I.Decoder.opcode
      (generatedJalrEncoding immediate rs1 rd) = 0b1100111#7 := by
    simp [RV32I.Decoder.opcode, generatedJalrEncoding]
    bv_decide
  have hfunct3 : RV32I.Decoder.funct3
      (generatedJalrEncoding immediate rs1 rd) = 0b000#3 := by
    simp [RV32I.Decoder.funct3, generatedJalrEncoding]
    bv_decide
  have hrd : RV32I.Decoder.rd
      (generatedJalrEncoding immediate rs1 rd) = rd := by
    clear hopcode hfunct3
    have bits : (generatedJalrEncoding immediate rs1 rd).extractLsb' 7 5 =
        BitVec.ofNat 5 rd.val := by
      simp [generatedJalrEncoding, encdec_reg_forwards, sailRegister,
        LeanRV32D.zero_extend, Sail.BitVec.zeroExtend]
      bv_decide
    simp [RV32I.Decoder.rd, bits]
  have hrs1 : RV32I.Decoder.rs1
      (generatedJalrEncoding immediate rs1 rd) = rs1 := by
    clear hopcode hfunct3 hrd
    have bits : (generatedJalrEncoding immediate rs1 rd).extractLsb' 15 5 =
        BitVec.ofNat 5 rs1.val := by
      simp [generatedJalrEncoding, encdec_reg_forwards, sailRegister,
        LeanRV32D.zero_extend, Sail.BitVec.zeroExtend]
      bv_decide
    simp [RV32I.Decoder.rs1, bits]
  have himmediate : RV32I.Decoder.iImmediate
      (generatedJalrEncoding immediate rs1 rd) = immediate := by
    clear hopcode hfunct3 hrd hrs1
    simp [RV32I.Decoder.iImmediate, generatedJalrEncoding]
    bv_decide
  simp [RV32I.Decoder.decode, hopcode, hfunct3, hrd, hrs1, himmediate]

/-! B-type words are parameterized by the twelve stored immediate bits.  The
architectural thirteen-bit displacement is recovered by appending its implicit
zero bit.  Keeping a raw-`funct3` form also lets the bridge state rejection of
the two encodings which the base ISA reserves. -/

def generatedBtypeEncodingWithFunct3 (storedImmediate : BitVec 12)
    (rs2 rs1 : RV32I.Register) (funct3 : BitVec 3) : RV32I.Word :=
  storedImmediate.extractLsb' 11 1 ++
    storedImmediate.extractLsb' 4 6 ++
    encdec_reg_forwards (sailRegister rs2) ++
    encdec_reg_forwards (sailRegister rs1) ++ funct3 ++
    storedImmediate.extractLsb' 0 4 ++
    storedImmediate.extractLsb' 10 1 ++ 0b1100011#7

def generatedBtypeEncoding (storedImmediate : BitVec 12)
    (rs2 rs1 : RV32I.Register) (operation : LeanRV32D.bop) : RV32I.Word :=
  generatedBtypeEncodingWithFunct3 storedImmediate rs2 rs1
    (encdec_bop_forwards operation)

@[simp] theorem generatedBtypeEncoding_bit31 (immediate : BitVec 12)
    (rs2 rs1 : RV32I.Register) (operation : LeanRV32D.bop) :
    Sail.BitVec.extractLsb
        (generatedBtypeEncoding immediate rs2 rs1 operation) 31 31 =
      immediate.extractLsb' 11 1 := by
  simp [generatedBtypeEncoding, generatedBtypeEncodingWithFunct3,
    Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedBtypeEncoding_bits30_25 (immediate : BitVec 12)
    (rs2 rs1 : RV32I.Register) (operation : LeanRV32D.bop) :
    Sail.BitVec.extractLsb
        (generatedBtypeEncoding immediate rs2 rs1 operation) 30 25 =
      immediate.extractLsb' 4 6 := by
  simp [generatedBtypeEncoding, generatedBtypeEncodingWithFunct3,
    Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedBtypeEncoding_rs2 (immediate : BitVec 12)
    (rs2 rs1 : RV32I.Register) (operation : LeanRV32D.bop) :
    Sail.BitVec.extractLsb
        (generatedBtypeEncoding immediate rs2 rs1 operation) 24 20 =
      encdec_reg_forwards (sailRegister rs2) := by
  simp [generatedBtypeEncoding, generatedBtypeEncodingWithFunct3,
    Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedBtypeEncoding_rs1 (immediate : BitVec 12)
    (rs2 rs1 : RV32I.Register) (operation : LeanRV32D.bop) :
    Sail.BitVec.extractLsb
        (generatedBtypeEncoding immediate rs2 rs1 operation) 19 15 =
      encdec_reg_forwards (sailRegister rs1) := by
  simp [generatedBtypeEncoding, generatedBtypeEncodingWithFunct3,
    Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedBtypeEncoding_funct3 (immediate : BitVec 12)
    (rs2 rs1 : RV32I.Register) (operation : LeanRV32D.bop) :
    Sail.BitVec.extractLsb
        (generatedBtypeEncoding immediate rs2 rs1 operation) 14 12 =
      encdec_bop_forwards operation := by
  simp [generatedBtypeEncoding, generatedBtypeEncodingWithFunct3,
    Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedBtypeEncoding_bits11_8 (immediate : BitVec 12)
    (rs2 rs1 : RV32I.Register) (operation : LeanRV32D.bop) :
    Sail.BitVec.extractLsb
        (generatedBtypeEncoding immediate rs2 rs1 operation) 11 8 =
      immediate.extractLsb' 0 4 := by
  simp [generatedBtypeEncoding, generatedBtypeEncodingWithFunct3,
    Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedBtypeEncoding_bit7 (immediate : BitVec 12)
    (rs2 rs1 : RV32I.Register) (operation : LeanRV32D.bop) :
    Sail.BitVec.extractLsb
        (generatedBtypeEncoding immediate rs2 rs1 operation) 7 7 =
      immediate.extractLsb' 10 1 := by
  simp [generatedBtypeEncoding, generatedBtypeEncodingWithFunct3,
    Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedBtypeEncoding_opcode (immediate : BitVec 12)
    (rs2 rs1 : RV32I.Register) (operation : LeanRV32D.bop) :
    Sail.BitVec.extractLsb
        (generatedBtypeEncoding immediate rs2 rs1 operation) 6 0 =
      0b1100011#7 := by
  simp [generatedBtypeEncoding, generatedBtypeEncodingWithFunct3,
    Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedBtypeImmediate_roundtrip (immediate : BitVec 12) :
    (((immediate.extractLsb' 11 1 +++ immediate.extractLsb' 10 1) +++
        immediate.extractLsb' 4 6) +++ immediate.extractLsb' 0 4) +++ 0#1 =
      immediate +++ 0#1 := by
  bv_decide

@[simp] theorem clean_decodes_generatedBtypeEncoding (immediate : BitVec 12)
    (rs2 rs1 : RV32I.Register) (operation : LeanRV32D.bop) :
    RV32I.Decoder.decode
        (generatedBtypeEncoding immediate rs2 rs1 operation) =
      some (cleanBranchInstruction operation rs1 rs2 (immediate ++ 0#1)) := by
  have hopcode : RV32I.Decoder.opcode
      (generatedBtypeEncoding immediate rs2 rs1 operation) = 0b1100011#7 := by
    simp [RV32I.Decoder.opcode, generatedBtypeEncoding,
      generatedBtypeEncodingWithFunct3]
    bv_decide
  have hfunct3 : RV32I.Decoder.funct3
      (generatedBtypeEncoding immediate rs2 rs1 operation) =
        encdec_bop_forwards operation := by
    simp [RV32I.Decoder.funct3, generatedBtypeEncoding,
      generatedBtypeEncodingWithFunct3]
    bv_decide
  have hrs2 : RV32I.Decoder.rs2
      (generatedBtypeEncoding immediate rs2 rs1 operation) = rs2 := by
    have bits :
        (generatedBtypeEncoding immediate rs2 rs1 operation).extractLsb' 20 5 =
          BitVec.ofNat 5 rs2.val := by
      simp [generatedBtypeEncoding, generatedBtypeEncodingWithFunct3,
        encdec_reg_forwards, sailRegister, LeanRV32D.zero_extend,
        Sail.BitVec.zeroExtend]
      bv_decide
    simp [RV32I.Decoder.rs2, bits]
  have hrs1 : RV32I.Decoder.rs1
      (generatedBtypeEncoding immediate rs2 rs1 operation) = rs1 := by
    have bits :
        (generatedBtypeEncoding immediate rs2 rs1 operation).extractLsb' 15 5 =
          BitVec.ofNat 5 rs1.val := by
      simp [generatedBtypeEncoding, generatedBtypeEncodingWithFunct3,
        encdec_reg_forwards, sailRegister, LeanRV32D.zero_extend,
        Sail.BitVec.zeroExtend]
      bv_decide
    simp [RV32I.Decoder.rs1, bits]
  have himmediate : RV32I.Decoder.bImmediate
      (generatedBtypeEncoding immediate rs2 rs1 operation) =
        immediate ++ 0#1 := by
    simp [RV32I.Decoder.bImmediate, generatedBtypeEncoding,
      generatedBtypeEncodingWithFunct3]
    bv_decide
  cases operation <;>
    simp only [RV32I.Decoder.decode, hopcode, hfunct3,
      encdec_bop_forwards, BitVec.toNat_ofNat, hrs1, hrs2, himmediate,
      cleanBranchInstruction]

@[simp] theorem clean_rejects_reservedBtype010 (immediate : BitVec 12)
    (rs2 rs1 : RV32I.Register) :
    RV32I.Decoder.decode
        (generatedBtypeEncodingWithFunct3 immediate rs2 rs1 0b010#3) = none := by
  have hopcode : RV32I.Decoder.opcode
      (generatedBtypeEncodingWithFunct3 immediate rs2 rs1 0b010#3) =
        0b1100011#7 := by
    simp [RV32I.Decoder.opcode, generatedBtypeEncodingWithFunct3]
    bv_decide
  have hfunct3 : RV32I.Decoder.funct3
      (generatedBtypeEncodingWithFunct3 immediate rs2 rs1 0b010#3) =
        0b010#3 := by
    simp [RV32I.Decoder.funct3, generatedBtypeEncodingWithFunct3]
    bv_decide
  simp [RV32I.Decoder.decode, hopcode, hfunct3]

@[simp] theorem clean_rejects_reservedBtype011 (immediate : BitVec 12)
    (rs2 rs1 : RV32I.Register) :
    RV32I.Decoder.decode
        (generatedBtypeEncodingWithFunct3 immediate rs2 rs1 0b011#3) = none := by
  have hopcode : RV32I.Decoder.opcode
      (generatedBtypeEncodingWithFunct3 immediate rs2 rs1 0b011#3) =
        0b1100011#7 := by
    simp [RV32I.Decoder.opcode, generatedBtypeEncodingWithFunct3]
    bv_decide
  have hfunct3 : RV32I.Decoder.funct3
      (generatedBtypeEncodingWithFunct3 immediate rs2 rs1 0b011#3) =
        0b011#3 := by
    simp [RV32I.Decoder.funct3, generatedBtypeEncodingWithFunct3]
    bv_decide
  simp [RV32I.Decoder.decode, hopcode, hfunct3]

/-! OP-IMM shares one physical I-type layout.  A raw-`funct3` constructor is
useful both for the ordinary generated `iop` mapping and for shift encodings,
whose operation is partly selected by the upper immediate bits. -/

def generatedItypeEncodingWithFunct3 (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) (funct3 : BitVec 3) : RV32I.Word :=
  immediate +++ encdec_reg_forwards (sailRegister rs1) +++ funct3 +++
    encdec_reg_forwards (sailRegister rd) +++ 0b0010011#7

def generatedItypeEncoding (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) (operation : LeanRV32D.iop) : RV32I.Word :=
  generatedItypeEncodingWithFunct3 immediate rs1 rd
    (encdec_iop_forwards operation)

/-- The generated ITYPE clause's operand decoder, named separately so proofs
can contract it without traversing the rest of the generated instruction
decoder. -/
def generatedItypeOperandDecode (word : RV32I.Word) :
    LeanRV32D.SailM (Option LeanRV32D.instruction) := do
  let rs1 ← encdec_reg_backwards (Sail.BitVec.extractLsb word 19 15)
  let operation ← encdec_iop_backwards (Sail.BitVec.extractLsb word 14 12)
  let rd ← encdec_reg_backwards (Sail.BitVec.extractLsb word 11 7)
  pure (some (.ITYPE
    (Sail.BitVec.extractLsb word 31 20, rs1, rd, operation)))

/-- Exactly the base ORI HINT words intercepted by the generated platform's
hard-enabled Zicbop decoder clause. -/
def ZicbopInterposes (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) : Prop :=
  let word := generatedItypeEncoding immediate rs1 rd .ORI
  (((encdec_cbop_zicbop_backwards_matches
        (Sail.BitVec.extractLsb word 24 20) &&
      encdec_reg_backwards_matches
        (Sail.BitVec.extractLsb word 19 15)) &&
    (Sail.BitVec.extractLsb word 14 0 == 0b110000000010011#15)) = true)

def generatedZicbopEncoding (upperImmediate : BitVec 7)
    (rs1 : RV32I.Register) (operation : LeanRV32D.cbop_zicbop) : RV32I.Word :=
  generatedItypeEncodingWithFunct3
    (upperImmediate ++ encdec_cbop_zicbop_forwards operation) rs1 0 0b110#3

/-- The generated Zicbop clause's operand decoder. -/
def generatedZicbopOperandDecode (word : RV32I.Word) :
    LeanRV32D.SailM (Option LeanRV32D.instruction) := do
  let operation ← encdec_cbop_zicbop_backwards
    (Sail.BitVec.extractLsb word 24 20)
  let rs1 ← encdec_reg_backwards (Sail.BitVec.extractLsb word 19 15)
  pure (some (.ZICBOP (operation, rs1,
    Sail.BitVec.extractLsb word 31 25 ++ 0#5)))

@[simp] theorem generatedZicbopEncoding_eq_itype_ori
    (upperImmediate : BitVec 7) (rs1 : RV32I.Register)
    (operation : LeanRV32D.cbop_zicbop) :
    generatedZicbopEncoding upperImmediate rs1 operation =
      generatedItypeEncoding
        (upperImmediate ++ encdec_cbop_zicbop_forwards operation) rs1 0 .ORI := by
  rfl

@[simp] theorem generatedItypeEncodingWithFunct3_immediate
    (immediate : BitVec 12) (rs1 rd : RV32I.Register) (funct3 : BitVec 3) :
    Sail.BitVec.extractLsb
        (generatedItypeEncodingWithFunct3 immediate rs1 rd funct3) 31 20 =
      immediate := by
  simp [generatedItypeEncodingWithFunct3, Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedItypeEncodingWithFunct3_rs1
    (immediate : BitVec 12) (rs1 rd : RV32I.Register) (funct3 : BitVec 3) :
    Sail.BitVec.extractLsb
        (generatedItypeEncodingWithFunct3 immediate rs1 rd funct3) 19 15 =
      encdec_reg_forwards (sailRegister rs1) := by
  simp [generatedItypeEncodingWithFunct3, Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedItypeEncodingWithFunct3_funct3
    (immediate : BitVec 12) (rs1 rd : RV32I.Register) (funct3 : BitVec 3) :
    Sail.BitVec.extractLsb
        (generatedItypeEncodingWithFunct3 immediate rs1 rd funct3) 14 12 =
      funct3 := by
  simp [generatedItypeEncodingWithFunct3, Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedItypeEncodingWithFunct3_rd
    (immediate : BitVec 12) (rs1 rd : RV32I.Register) (funct3 : BitVec 3) :
    Sail.BitVec.extractLsb
        (generatedItypeEncodingWithFunct3 immediate rs1 rd funct3) 11 7 =
      encdec_reg_forwards (sailRegister rd) := by
  simp [generatedItypeEncodingWithFunct3, Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedItypeEncodingWithFunct3_opcode
    (immediate : BitVec 12) (rs1 rd : RV32I.Register) (funct3 : BitVec 3) :
    Sail.BitVec.extractLsb
        (generatedItypeEncodingWithFunct3 immediate rs1 rd funct3) 6 0 =
      0b0010011#7 := by
  simp [generatedItypeEncodingWithFunct3, Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedItypeEncoding_immediate
    (immediate : BitVec 12) (rs1 rd : RV32I.Register)
    (operation : LeanRV32D.iop) :
    Sail.BitVec.extractLsb
        (generatedItypeEncoding immediate rs1 rd operation) 31 20 =
      immediate := by
  simp [generatedItypeEncoding]

@[simp] theorem generatedItypeEncoding_rs1
    (immediate : BitVec 12) (rs1 rd : RV32I.Register)
    (operation : LeanRV32D.iop) :
    Sail.BitVec.extractLsb
        (generatedItypeEncoding immediate rs1 rd operation) 19 15 =
      encdec_reg_forwards (sailRegister rs1) := by
  simp [generatedItypeEncoding]

@[simp] theorem generatedItypeEncoding_funct3
    (immediate : BitVec 12) (rs1 rd : RV32I.Register)
    (operation : LeanRV32D.iop) :
    Sail.BitVec.extractLsb
        (generatedItypeEncoding immediate rs1 rd operation) 14 12 =
      encdec_iop_forwards operation := by
  simp [generatedItypeEncoding]

@[simp] theorem generatedItypeEncoding_rd
    (immediate : BitVec 12) (rs1 rd : RV32I.Register)
    (operation : LeanRV32D.iop) :
    Sail.BitVec.extractLsb
        (generatedItypeEncoding immediate rs1 rd operation) 11 7 =
      encdec_reg_forwards (sailRegister rd) := by
  simp [generatedItypeEncoding]

@[simp] theorem generatedItypeEncoding_opcode
    (immediate : BitVec 12) (rs1 rd : RV32I.Register)
    (operation : LeanRV32D.iop) :
    Sail.BitVec.extractLsb
        (generatedItypeEncoding immediate rs1 rd operation) 6 0 =
      0b0010011#7 := by
  simp [generatedItypeEncoding]

@[simp] theorem generatedItypeEncoding_zicbop_operation
    (immediate : BitVec 12) (rs1 rd : RV32I.Register) :
    Sail.BitVec.extractLsb
        (generatedItypeEncoding immediate rs1 rd .ORI) 24 20 =
      immediate.extractLsb' 0 5 := by
  simp [generatedItypeEncoding, generatedItypeEncodingWithFunct3,
    encdec_iop_forwards, Sail.BitVec.extractLsb, BitVec.extractLsb]
  bv_decide

private theorem extractItypeLow15 (immediate : BitVec 12)
    (rs1 : BitVec 5) (funct3 : BitVec 3) (rd : BitVec 5)
    (opcode : BitVec 7) :
    (immediate ++ rs1 ++ funct3 ++ rd ++ opcode).extractLsb' 0 15 =
      funct3 ++ rd ++ opcode := by
  bv_decide

@[simp] theorem generatedItypeEncoding_zicbop_low15
    (immediate : BitVec 12) (rs1 rd : RV32I.Register) :
    (generatedItypeEncoding immediate rs1 rd .ORI).extractLsb' 0 15 =
      0b110#3 ++ encdec_reg_forwards (sailRegister rd) ++ 0b0010011#7 := by
  simpa [generatedItypeEncoding, generatedItypeEncodingWithFunct3,
    encdec_iop_forwards] using
      extractItypeLow15 immediate
        (encdec_reg_forwards (sailRegister rs1)) 0b110#3
        (encdec_reg_forwards (sailRegister rd)) 0b0010011#7

@[simp] theorem generatedItypeEncoding_zicbop_low15_sail
    (immediate : BitVec 12) (rs1 rd : RV32I.Register) :
    Sail.BitVec.extractLsb
        (generatedItypeEncoding immediate rs1 rd .ORI) 14 0 =
      0b110#3 ++ encdec_reg_forwards (sailRegister rd) ++ 0b0010011#7 := by
  simpa only [Sail.BitVec.extractLsb, BitVec.extractLsb] using
    generatedItypeEncoding_zicbop_low15 immediate rs1 rd

theorem ZicbopInterposes_iff (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) :
    ZicbopInterposes immediate rs1 rd ↔
      encdec_cbop_zicbop_backwards_matches
          (immediate.extractLsb' 0 5) = true ∧
        encdec_reg_forwards (sailRegister rd) = 0#5 := by
  unfold ZicbopInterposes
  simp only
  rw [generatedItypeEncoding_zicbop_operation,
    generatedItypeEncoding_rs1,
    generatedItypeEncoding_zicbop_low15_sail]
  simp only [encdec_reg_backwards_matches_rv32, Bool.and_true]
  bv_decide

theorem encodedRegister_eq_zero_iff (rd : RV32I.Register) :
    encdec_reg_forwards (sailRegister rd) = 0#5 ↔ rd = 0 := by
  constructor
  · intro encoded
    apply Fin.ext
    have values := congrArg BitVec.toNat encoded
    simpa [encdec_reg_forwards, sailRegister, LeanRV32D.zero_extend,
      Sail.BitVec.zeroExtend] using values
  · intro zero
    subst rd
    exact encdec_reg_forwards_zero

/-- Every ORI word intercepted by Zicbop has one of the three symbolic
prefetch encodings; together with the negated guard used by
`generated_decodes_ori`, this makes the ORI split exhaustive. -/
theorem ZicbopInterposes.decompose (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) (interposes : ZicbopInterposes immediate rs1 rd) :
    ∃ upperImmediate : BitVec 7, ∃ operation : LeanRV32D.cbop_zicbop,
      rd = 0 ∧
        immediate = upperImmediate ++ encdec_cbop_zicbop_forwards operation := by
  rw [ZicbopInterposes_iff] at interposes
  rcases interposes with ⟨guardMatches, encodedRd⟩
  have rdZero : rd = 0 := (encodedRegister_eq_zero_iff rd).mp encodedRd
  rcases (encdec_cbop_zicbop_matcher_characterization
      (immediate.extractLsb' 0 5)).mp guardMatches with low | low | low
  · refine ⟨immediate.extractLsb' 5 7, .PREFETCH_I, rdZero, ?_⟩
    simp only [encdec_cbop_zicbop_forwards]
    bv_decide
  · refine ⟨immediate.extractLsb' 5 7, .PREFETCH_R, rdZero, ?_⟩
    simp only [encdec_cbop_zicbop_forwards]
    bv_decide
  · refine ⟨immediate.extractLsb' 5 7, .PREFETCH_W, rdZero, ?_⟩
    simp only [encdec_cbop_zicbop_forwards]
    bv_decide

@[simp] theorem generatedZicbopEncoding_operation
    (upperImmediate : BitVec 7) (rs1 : RV32I.Register)
    (operation : LeanRV32D.cbop_zicbop) :
    Sail.BitVec.extractLsb
        (generatedZicbopEncoding upperImmediate rs1 operation) 24 20 =
      encdec_cbop_zicbop_forwards operation := by
  cases operation <;>
    simp [generatedZicbopEncoding, generatedItypeEncodingWithFunct3,
      Sail.BitVec.extractLsb] <;>
    bv_decide

@[simp] theorem generatedZicbopEncoding_rs1
    (upperImmediate : BitVec 7) (rs1 : RV32I.Register)
    (operation : LeanRV32D.cbop_zicbop) :
    Sail.BitVec.extractLsb
        (generatedZicbopEncoding upperImmediate rs1 operation) 19 15 =
      encdec_reg_forwards (sailRegister rs1) := by
  simp only [generatedZicbopEncoding,
    generatedItypeEncodingWithFunct3_rs1]

@[simp] theorem generatedZicbopEncoding_low15
    (upperImmediate : BitVec 7) (rs1 : RV32I.Register)
    (operation : LeanRV32D.cbop_zicbop) :
    Sail.BitVec.extractLsb
        (generatedZicbopEncoding upperImmediate rs1 operation) 14 0 =
      0b110000000010011#15 := by
  cases operation <;>
    simp [generatedZicbopEncoding, generatedItypeEncodingWithFunct3,
      Sail.BitVec.extractLsb, encdec_reg_forwards_zero] <;>
    bv_decide

@[simp] theorem generatedZicbopEncoding_upper
    (upperImmediate : BitVec 7) (rs1 : RV32I.Register)
    (operation : LeanRV32D.cbop_zicbop) :
    Sail.BitVec.extractLsb
        (generatedZicbopEncoding upperImmediate rs1 operation) 31 25 =
      upperImmediate := by
  cases operation <;>
    simp [generatedZicbopEncoding, generatedItypeEncodingWithFunct3,
      Sail.BitVec.extractLsb] <;>
    bv_decide

@[simp] theorem generatedZicbopEncoding_operation_core
    (upperImmediate : BitVec 7) (rs1 : RV32I.Register)
    (operation : LeanRV32D.cbop_zicbop) :
    (generatedZicbopEncoding upperImmediate rs1 operation).extractLsb' 20 5 =
      encdec_cbop_zicbop_forwards operation := by
  cases operation <;>
    simp [generatedZicbopEncoding, generatedItypeEncodingWithFunct3] <;>
    bv_decide

@[simp] theorem generatedZicbopEncoding_rs1_core
    (upperImmediate : BitVec 7) (rs1 : RV32I.Register)
    (operation : LeanRV32D.cbop_zicbop) :
    (generatedZicbopEncoding upperImmediate rs1 operation).extractLsb' 15 5 =
      encdec_reg_forwards (sailRegister rs1) := by
  simp [generatedZicbopEncoding, generatedItypeEncodingWithFunct3]
  bv_decide

@[simp] theorem generatedZicbopEncoding_low15_core
    (upperImmediate : BitVec 7) (rs1 : RV32I.Register)
    (operation : LeanRV32D.cbop_zicbop) :
    (generatedZicbopEncoding upperImmediate rs1 operation).extractLsb' 0 15 =
      0b110000000010011#15 := by
  cases operation <;>
    simp [generatedZicbopEncoding, generatedItypeEncodingWithFunct3,
      encdec_reg_forwards_zero] <;>
    bv_decide

@[simp] theorem generatedZicbop_guard_true
    (upperImmediate : BitVec 7) (rs1 : RV32I.Register)
    (operation : LeanRV32D.cbop_zicbop) :
    (((encdec_cbop_zicbop_backwards_matches
          (Sail.BitVec.extractLsb
            (generatedZicbopEncoding upperImmediate rs1 operation) 24 20) &&
        encdec_reg_backwards_matches
          (Sail.BitVec.extractLsb
            (generatedZicbopEncoding upperImmediate rs1 operation) 19 15)) &&
      (Sail.BitVec.extractLsb
        (generatedZicbopEncoding upperImmediate rs1 operation) 14 0 ==
          0b110000000010011#15)) = true) := by
  cases operation <;>
    simp only [generatedZicbopEncoding_operation,
      generatedZicbopEncoding_rs1,
      generatedZicbopEncoding_low15,
      encdec_cbop_zicbop_forwards,
      encdec_cbop_zicbop_backwards_matches,
      encdec_reg_backwards_matches_rv32, Bool.true_and,
      beq_self_eq_true]

theorem generatedZicbopEncoding_interposes (upperImmediate : BitVec 7)
    (rs1 : RV32I.Register) (operation : LeanRV32D.cbop_zicbop) :
    ZicbopInterposes
      (upperImmediate ++ encdec_cbop_zicbop_forwards operation) rs1 0 := by
  unfold ZicbopInterposes
  rw [← generatedZicbopEncoding_eq_itype_ori]
  exact generatedZicbop_guard_true upperImmediate rs1 operation

theorem zicbopInterposes_or_not (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) :
    ZicbopInterposes immediate rs1 rd ∨
      ¬ ZicbopInterposes immediate rs1 rd :=
  Classical.em _

@[simp] theorem generatedZicbopOperandDecode_encoding
    (upperImmediate : BitVec 7) (rs1 : RV32I.Register)
    (operation : LeanRV32D.cbop_zicbop) (sail : SailState) :
    generatedZicbopOperandDecode
        (generatedZicbopEncoding upperImmediate rs1 operation) sail =
      .ok (some (.ZICBOP
        (operation, sailRegister rs1, upperImmediate ++ 0#5))) sail := by
  cases operation <;>
    simp only [generatedZicbopOperandDecode,
      generatedZicbopEncoding_operation, generatedZicbopEncoding_rs1,
      generatedZicbopEncoding_upper, encdec_cbop_zicbop_roundtrip,
      encdec_reg_roundtrip, bind, EStateM.bind, pure, EStateM.pure]

@[simp] theorem generatedItypeOperandDecode_encoding
    (immediate : BitVec 12) (rs1 rd : RV32I.Register)
    (operation : LeanRV32D.iop) (sail : SailState) :
    generatedItypeOperandDecode
        (generatedItypeEncoding immediate rs1 rd operation) sail =
      .ok (some (.ITYPE
        (immediate, sailRegister rs1, sailRegister rd, operation))) sail := by
  simp [generatedItypeOperandDecode, bind, EStateM.bind, pure, EStateM.pure]

@[simp] theorem clean_decodes_generatedItypeEncoding (immediate : BitVec 12)
    (rs1 rd : RV32I.Register) (operation : LeanRV32D.iop) :
    RV32I.Decoder.decode
        (generatedItypeEncoding immediate rs1 rd operation) =
      some (cleanItypeInstruction operation rd rs1 immediate) := by
  have hopcode : RV32I.Decoder.opcode
      (generatedItypeEncoding immediate rs1 rd operation) = 0b0010011#7 := by
    simp [RV32I.Decoder.opcode, generatedItypeEncoding,
      generatedItypeEncodingWithFunct3]
    bv_decide
  have hfunct3 : RV32I.Decoder.funct3
      (generatedItypeEncoding immediate rs1 rd operation) =
        encdec_iop_forwards operation := by
    simp [RV32I.Decoder.funct3, generatedItypeEncoding,
      generatedItypeEncodingWithFunct3]
    bv_decide
  have hrd : RV32I.Decoder.rd
      (generatedItypeEncoding immediate rs1 rd operation) = rd := by
    have bits :
        (generatedItypeEncoding immediate rs1 rd operation).extractLsb' 7 5 =
          BitVec.ofNat 5 rd.val := by
      simp [generatedItypeEncoding, generatedItypeEncodingWithFunct3,
        encdec_reg_forwards, sailRegister, LeanRV32D.zero_extend,
        Sail.BitVec.zeroExtend]
      bv_decide
    simp [RV32I.Decoder.rd, bits]
  have hrs1 : RV32I.Decoder.rs1
      (generatedItypeEncoding immediate rs1 rd operation) = rs1 := by
    have bits :
        (generatedItypeEncoding immediate rs1 rd operation).extractLsb' 15 5 =
          BitVec.ofNat 5 rs1.val := by
      simp [generatedItypeEncoding, generatedItypeEncodingWithFunct3,
        encdec_reg_forwards, sailRegister, LeanRV32D.zero_extend,
        Sail.BitVec.zeroExtend]
      bv_decide
    simp [RV32I.Decoder.rs1, bits]
  have himmediate : RV32I.Decoder.iImmediate
      (generatedItypeEncoding immediate rs1 rd operation) = immediate := by
    simp [RV32I.Decoder.iImmediate, generatedItypeEncoding,
      generatedItypeEncodingWithFunct3]
    bv_decide
  cases operation <;>
    simp only [RV32I.Decoder.decode, hopcode, hfunct3,
      encdec_iop_forwards, BitVec.toNat_ofNat, hrd, hrs1, himmediate,
      cleanItypeInstruction]

@[simp] theorem clean_decodes_generatedZicbopEncoding
    (upperImmediate : BitVec 7) (rs1 : RV32I.Register)
    (operation : LeanRV32D.cbop_zicbop) :
    RV32I.Decoder.decode (generatedZicbopEncoding upperImmediate rs1 operation) =
      some (.ori 0 rs1
        (upperImmediate ++ encdec_cbop_zicbop_forwards operation)) := by
  rw [generatedZicbopEncoding_eq_itype_ori,
    clean_decodes_generatedItypeEncoding]
  rfl

def generatedShiftUpper : LeanRV32D.sop → BitVec 7
  | .SLLI | .SRLI => 0b0000000#7
  | .SRAI => 0b0100000#7

def generatedShiftEncoding (shamt : BitVec 5)
    (rs1 rd : RV32I.Register) (operation : LeanRV32D.sop) : RV32I.Word :=
  generatedItypeEncodingWithFunct3
    (generatedShiftUpper operation ++ shamt) rs1 rd
    (encdec_sop_forwards operation)

/-- The common operand and RV32 shift-amount check used by each generated
SHIFTIOP clause. -/
def generatedShiftOperandDecode (word : RV32I.Word)
    (operation : LeanRV32D.sop) :
    LeanRV32D.SailM (Option LeanRV32D.instruction) := do
  let shamt := Sail.BitVec.extractLsb word 25 20
  let rs1 ← encdec_reg_backwards (Sail.BitVec.extractLsb word 19 15)
  let rd ← encdec_reg_backwards (Sail.BitVec.extractLsb word 11 7)
  if ((LeanRV32D.Functions.xlen == 64) ||
      (Sail.BitVec.access shamt 5 == 0#1)) then
    pure (some (.SHIFTIOP (shamt, rs1, rd, operation)))
  else
    pure none

@[simp] theorem generatedShiftEncoding_funct6 (shamt : BitVec 5)
    (rs1 rd : RV32I.Register) (operation : LeanRV32D.sop) :
    Sail.BitVec.extractLsb
        (generatedShiftEncoding shamt rs1 rd operation) 31 26 =
      (generatedShiftUpper operation).extractLsb' 1 6 := by
  simp [generatedShiftEncoding, generatedItypeEncodingWithFunct3,
    Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedShiftEncoding_shamt (shamt : BitVec 5)
    (rs1 rd : RV32I.Register) (operation : LeanRV32D.sop) :
    Sail.BitVec.extractLsb
        (generatedShiftEncoding shamt rs1 rd operation) 25 20 =
      0#1 ++ shamt := by
  simp [generatedShiftEncoding, generatedItypeEncodingWithFunct3,
    generatedShiftUpper, Sail.BitVec.extractLsb]
  cases operation <;> bv_decide

@[simp] theorem generatedShiftEncoding_rs1 (shamt : BitVec 5)
    (rs1 rd : RV32I.Register) (operation : LeanRV32D.sop) :
    Sail.BitVec.extractLsb
        (generatedShiftEncoding shamt rs1 rd operation) 19 15 =
      encdec_reg_forwards (sailRegister rs1) := by
  simp [generatedShiftEncoding]

@[simp] theorem generatedShiftEncoding_funct3 (shamt : BitVec 5)
    (rs1 rd : RV32I.Register) (operation : LeanRV32D.sop) :
    Sail.BitVec.extractLsb
        (generatedShiftEncoding shamt rs1 rd operation) 14 12 =
      encdec_sop_forwards operation := by
  simp [generatedShiftEncoding]

@[simp] theorem generatedShiftEncoding_rd (shamt : BitVec 5)
    (rs1 rd : RV32I.Register) (operation : LeanRV32D.sop) :
    Sail.BitVec.extractLsb
        (generatedShiftEncoding shamt rs1 rd operation) 11 7 =
      encdec_reg_forwards (sailRegister rd) := by
  simp [generatedShiftEncoding]

@[simp] theorem generatedShiftEncoding_opcode (shamt : BitVec 5)
    (rs1 rd : RV32I.Register) (operation : LeanRV32D.sop) :
    Sail.BitVec.extractLsb
        (generatedShiftEncoding shamt rs1 rd operation) 6 0 =
      0b0010011#7 := by
  simp [generatedShiftEncoding]

@[simp] theorem generatedShiftOperandDecode_encoding (shamt : BitVec 5)
    (rs1 rd : RV32I.Register) (operation : LeanRV32D.sop)
    (sail : SailState) :
    generatedShiftOperandDecode
        (generatedShiftEncoding shamt rs1 rd operation) operation sail =
      .ok (some (.SHIFTIOP
        (0#1 ++ shamt, sailRegister rs1, sailRegister rd, operation))) sail := by
  have highBit : BitVec.ofBool (0#1 ++ shamt)[5] = 0#1 := by
    bv_decide
  simp [generatedShiftOperandDecode, bind, EStateM.bind, pure, EStateM.pure,
    LeanRV32D.Functions.xlen, Sail.BitVec.access, highBit]

@[simp] theorem clean_decodes_generatedShiftEncoding (shamt : BitVec 5)
    (rs1 rd : RV32I.Register) (operation : LeanRV32D.sop) :
    RV32I.Decoder.decode (generatedShiftEncoding shamt rs1 rd operation) =
      some (cleanShiftInstruction operation rd rs1 shamt) := by
  have hopcode : RV32I.Decoder.opcode
      (generatedShiftEncoding shamt rs1 rd operation) = 0b0010011#7 := by
    simp [RV32I.Decoder.opcode, generatedShiftEncoding,
      generatedItypeEncodingWithFunct3]
    bv_decide
  have hfunct3 : RV32I.Decoder.funct3
      (generatedShiftEncoding shamt rs1 rd operation) =
        encdec_sop_forwards operation := by
    simp [RV32I.Decoder.funct3, generatedShiftEncoding,
      generatedItypeEncodingWithFunct3]
    bv_decide
  have hfunct7 : RV32I.Decoder.funct7
      (generatedShiftEncoding shamt rs1 rd operation) =
        generatedShiftUpper operation := by
    simp [RV32I.Decoder.funct7, generatedShiftEncoding,
      generatedItypeEncodingWithFunct3]
    bv_decide
  have hrd : RV32I.Decoder.rd
      (generatedShiftEncoding shamt rs1 rd operation) = rd := by
    have bits :
        (generatedShiftEncoding shamt rs1 rd operation).extractLsb' 7 5 =
          BitVec.ofNat 5 rd.val := by
      simp [generatedShiftEncoding, generatedItypeEncodingWithFunct3,
        encdec_reg_forwards, sailRegister, LeanRV32D.zero_extend,
        Sail.BitVec.zeroExtend]
      bv_decide
    simp [RV32I.Decoder.rd, bits]
  have hrs1 : RV32I.Decoder.rs1
      (generatedShiftEncoding shamt rs1 rd operation) = rs1 := by
    have bits :
        (generatedShiftEncoding shamt rs1 rd operation).extractLsb' 15 5 =
          BitVec.ofNat 5 rs1.val := by
      simp [generatedShiftEncoding, generatedItypeEncodingWithFunct3,
        encdec_reg_forwards, sailRegister, LeanRV32D.zero_extend,
        Sail.BitVec.zeroExtend]
      bv_decide
    simp [RV32I.Decoder.rs1, bits]
  have hshamt :
      (generatedShiftEncoding shamt rs1 rd operation).extractLsb' 20 5 =
        shamt := by
    simp [generatedShiftEncoding, generatedItypeEncodingWithFunct3,
      generatedShiftUpper]
    cases operation <;> bv_decide
  cases operation <;>
    simp only [RV32I.Decoder.decode, hopcode, hfunct3, hfunct7,
      generatedShiftUpper, encdec_sop_forwards, BitVec.toNat_ofNat,
      hrd, hrs1, hshamt, cleanShiftInstruction]

/-! For RV32, every other upper-seven-bit pattern is reserved.  The generated
shift clauses test the upper six bits and then the high bit of their six-bit
shift amount; together those tests accept exactly the same upper-seven-bit
values as the clean decoder. -/

theorem generated_slli_guards_reject_reserved (upper : BitVec 7)
    (shamt : BitVec 5) (reserved : upper ≠ 0b0000000#7) :
    ¬ (upper.extractLsb' 1 6 = 0b000000#6 ∧
      Sail.BitVec.access (upper.extractLsb' 0 1 ++ shamt) 5 = 0#1) := by
  intro hmatches
  apply reserved
  rcases hmatches with ⟨high, low⟩
  simp [Sail.BitVec.access] at low
  bv_decide

theorem generated_srli_guards_reject_reserved (upper : BitVec 7)
    (shamt : BitVec 5) (reserved : upper ≠ 0b0000000#7) :
    ¬ (upper.extractLsb' 1 6 = 0b000000#6 ∧
      Sail.BitVec.access (upper.extractLsb' 0 1 ++ shamt) 5 = 0#1) :=
  generated_slli_guards_reject_reserved upper shamt reserved

theorem generated_srai_guards_reject_reserved (upper : BitVec 7)
    (shamt : BitVec 5) (reserved : upper ≠ 0b0100000#7) :
    ¬ (upper.extractLsb' 1 6 = 0b010000#6 ∧
      Sail.BitVec.access (upper.extractLsb' 0 1 ++ shamt) 5 = 0#1) := by
  intro hmatches
  apply reserved
  rcases hmatches with ⟨high, low⟩
  simp [Sail.BitVec.access] at low
  bv_decide

theorem clean_rejects_reservedSlli (upper : BitVec 7) (shamt : BitVec 5)
    (rs1 rd : RV32I.Register) (reserved : upper ≠ 0b0000000#7) :
    RV32I.Decoder.decode
        (generatedItypeEncodingWithFunct3 (upper ++ shamt) rs1 rd 0b001#3) =
      none := by
  have hopcode : RV32I.Decoder.opcode
      (generatedItypeEncodingWithFunct3 (upper ++ shamt) rs1 rd 0b001#3) =
        0b0010011#7 := by
    simp [RV32I.Decoder.opcode, generatedItypeEncodingWithFunct3]
    bv_decide
  have hfunct3 : RV32I.Decoder.funct3
      (generatedItypeEncodingWithFunct3 (upper ++ shamt) rs1 rd 0b001#3) =
        0b001#3 := by
    simp [RV32I.Decoder.funct3, generatedItypeEncodingWithFunct3]
    bv_decide
  have hfunct7 : RV32I.Decoder.funct7
      (generatedItypeEncodingWithFunct3 (upper ++ shamt) rs1 rd 0b001#3) =
        upper := by
    simp [RV32I.Decoder.funct7, generatedItypeEncodingWithFunct3]
    bv_decide
  have upperNat : upper.toNat ≠ 0 := by
    intro equal
    apply reserved
    apply BitVec.eq_of_toNat_eq
    simpa using equal
  simp [RV32I.Decoder.decode, hopcode, hfunct3, hfunct7, upperNat]

theorem clean_rejects_reservedRightShift (upper : BitVec 7) (shamt : BitVec 5)
    (rs1 rd : RV32I.Register)
    (notSrli : upper ≠ 0b0000000#7) (notSrai : upper ≠ 0b0100000#7) :
    RV32I.Decoder.decode
        (generatedItypeEncodingWithFunct3 (upper ++ shamt) rs1 rd 0b101#3) =
      none := by
  have hopcode : RV32I.Decoder.opcode
      (generatedItypeEncodingWithFunct3 (upper ++ shamt) rs1 rd 0b101#3) =
        0b0010011#7 := by
    simp [RV32I.Decoder.opcode, generatedItypeEncodingWithFunct3]
    bv_decide
  have hfunct3 : RV32I.Decoder.funct3
      (generatedItypeEncodingWithFunct3 (upper ++ shamt) rs1 rd 0b101#3) =
        0b101#3 := by
    simp [RV32I.Decoder.funct3, generatedItypeEncodingWithFunct3]
    bv_decide
  have hfunct7 : RV32I.Decoder.funct7
      (generatedItypeEncodingWithFunct3 (upper ++ shamt) rs1 rd 0b101#3) =
        upper := by
    simp [RV32I.Decoder.funct7, generatedItypeEncodingWithFunct3]
    bv_decide
  have upperNatZero : upper.toNat ≠ 0 := by
    intro equal
    apply notSrli
    apply BitVec.eq_of_toNat_eq
    simpa using equal
  have upperNatSrai : upper.toNat ≠ 0b0100000 := by
    intro equal
    apply notSrai
    apply BitVec.eq_of_toNat_eq
    simpa using equal
  simp [RV32I.Decoder.decode, hopcode, hfunct3, hfunct7,
    upperNatZero, upperNatSrai]

/-! OP has the ordinary R-type layout.  Sail spells out its ten base
operations as separate decoder clauses, so the bridge records their two
discriminating fields explicitly. -/

def generatedRtypeFunct3 : LeanRV32D.rop → BitVec 3
  | .ADD | .SUB => 0b000
  | .SLL => 0b001
  | .SLT => 0b010
  | .SLTU => 0b011
  | .XOR => 0b100
  | .SRL | .SRA => 0b101
  | .OR => 0b110
  | .AND => 0b111

def generatedRtypeFunct7 : LeanRV32D.rop → BitVec 7
  | .SUB | .SRA => 0b0100000
  | _ => 0b0000000

def generatedRtypeEncodingWithFields (funct7 : BitVec 7)
    (rs2 rs1 rd : RV32I.Register) (funct3 : BitVec 3) : RV32I.Word :=
  funct7 ++ encdec_reg_forwards (sailRegister rs2) ++
    encdec_reg_forwards (sailRegister rs1) ++ funct3 ++
    encdec_reg_forwards (sailRegister rd) ++ 0b0110011#7

def generatedRtypeEncoding (rs2 rs1 rd : RV32I.Register)
    (operation : LeanRV32D.rop) : RV32I.Word :=
  generatedRtypeEncodingWithFields (generatedRtypeFunct7 operation)
    rs2 rs1 rd (generatedRtypeFunct3 operation)

/-- The three-register operand decoder shared by the generated base RTYPE
clauses, named so the generated-boundary proof can contract it locally. -/
def generatedRtypeOperandDecode (word : RV32I.Word)
    (operation : LeanRV32D.rop) :
    LeanRV32D.SailM (Option LeanRV32D.instruction) := do
  let rs2 ← encdec_reg_backwards (Sail.BitVec.extractLsb word 24 20)
  let rs1 ← encdec_reg_backwards (Sail.BitVec.extractLsb word 19 15)
  let rd ← encdec_reg_backwards (Sail.BitVec.extractLsb word 11 7)
  pure (some (.RTYPE (rs2, rs1, rd, operation)))

@[simp] theorem generatedRtypeEncodingWithFields_funct7 (funct7 : BitVec 7)
    (rs2 rs1 rd : RV32I.Register) (funct3 : BitVec 3) :
    Sail.BitVec.extractLsb
        (generatedRtypeEncodingWithFields funct7 rs2 rs1 rd funct3) 31 25 =
      funct7 := by
  simp [generatedRtypeEncodingWithFields, Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedRtypeEncodingWithFields_rs2 (funct7 : BitVec 7)
    (rs2 rs1 rd : RV32I.Register) (funct3 : BitVec 3) :
    Sail.BitVec.extractLsb
        (generatedRtypeEncodingWithFields funct7 rs2 rs1 rd funct3) 24 20 =
      encdec_reg_forwards (sailRegister rs2) := by
  simp [generatedRtypeEncodingWithFields, Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedRtypeEncodingWithFields_rs2_core (funct7 : BitVec 7)
    (rs2 rs1 rd : RV32I.Register) (funct3 : BitVec 3) :
    (generatedRtypeEncodingWithFields funct7 rs2 rs1 rd funct3).extractLsb'
        20 5 = encdec_reg_forwards (sailRegister rs2) := by
  simp [generatedRtypeEncodingWithFields]
  bv_decide

@[simp] theorem generatedRtypeEncodingWithFields_funct7_core (funct7 : BitVec 7)
    (rs2 rs1 rd : RV32I.Register) (funct3 : BitVec 3) :
    (generatedRtypeEncodingWithFields funct7 rs2 rs1 rd funct3).extractLsb'
        25 7 = funct7 := by
  simp [generatedRtypeEncodingWithFields]
  bv_decide

@[simp] theorem generatedRtypeEncodingWithFields_rs1 (funct7 : BitVec 7)
    (rs2 rs1 rd : RV32I.Register) (funct3 : BitVec 3) :
    Sail.BitVec.extractLsb
        (generatedRtypeEncodingWithFields funct7 rs2 rs1 rd funct3) 19 15 =
      encdec_reg_forwards (sailRegister rs1) := by
  simp [generatedRtypeEncodingWithFields, Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedRtypeEncodingWithFields_funct3 (funct7 : BitVec 7)
    (rs2 rs1 rd : RV32I.Register) (funct3 : BitVec 3) :
    Sail.BitVec.extractLsb
        (generatedRtypeEncodingWithFields funct7 rs2 rs1 rd funct3) 14 12 =
      funct3 := by
  simp [generatedRtypeEncodingWithFields, Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedRtypeEncodingWithFields_rd (funct7 : BitVec 7)
    (rs2 rs1 rd : RV32I.Register) (funct3 : BitVec 3) :
    Sail.BitVec.extractLsb
        (generatedRtypeEncodingWithFields funct7 rs2 rs1 rd funct3) 11 7 =
      encdec_reg_forwards (sailRegister rd) := by
  simp [generatedRtypeEncodingWithFields, Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedRtypeEncodingWithFields_opcode (funct7 : BitVec 7)
    (rs2 rs1 rd : RV32I.Register) (funct3 : BitVec 3) :
    Sail.BitVec.extractLsb
        (generatedRtypeEncodingWithFields funct7 rs2 rs1 rd funct3) 6 0 =
      0b0110011#7 := by
  simp [generatedRtypeEncodingWithFields, Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedRtypeEncodingWithFields_opcode_core (funct7 : BitVec 7)
    (rs2 rs1 rd : RV32I.Register) (funct3 : BitVec 3) :
    (generatedRtypeEncodingWithFields funct7 rs2 rs1 rd funct3).extractLsb'
        0 7 = 0b0110011#7 := by
  simp [generatedRtypeEncodingWithFields]
  bv_decide

@[simp] theorem generatedRtypeEncodingWithFields_low20 (funct7 : BitVec 7)
    (rs2 rs1 rd : RV32I.Register) (funct3 : BitVec 3) :
    Sail.BitVec.extractLsb
        (generatedRtypeEncodingWithFields funct7 rs2 rs1 rd funct3) 19 0 =
      encdec_reg_forwards (sailRegister rs1) ++ funct3 ++
        encdec_reg_forwards (sailRegister rd) ++ 0b0110011#7 := by
  simp [generatedRtypeEncodingWithFields, Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedRtypeEncodingWithFields_low20_core (funct7 : BitVec 7)
    (rs2 rs1 rd : RV32I.Register) (funct3 : BitVec 3) :
    (generatedRtypeEncodingWithFields funct7 rs2 rs1 rd funct3).extractLsb'
        0 20 = encdec_reg_forwards (sailRegister rs1) ++ funct3 ++
          encdec_reg_forwards (sailRegister rd) ++ 0b0110011#7 := by
  simp [generatedRtypeEncodingWithFields]
  bv_decide

@[simp] theorem generatedRtypeEncodingWithFields_low15 (funct7 : BitVec 7)
    (rs2 rs1 rd : RV32I.Register) (funct3 : BitVec 3) :
    Sail.BitVec.extractLsb
        (generatedRtypeEncodingWithFields funct7 rs2 rs1 rd funct3) 14 0 =
      funct3 ++ encdec_reg_forwards (sailRegister rd) ++ 0b0110011#7 := by
  simp [generatedRtypeEncodingWithFields, Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedRtypeEncodingWithFields_low15_core (funct7 : BitVec 7)
    (rs2 rs1 rd : RV32I.Register) (funct3 : BitVec 3) :
    (generatedRtypeEncodingWithFields funct7 rs2 rs1 rd funct3).extractLsb'
        0 15 = funct3 ++ encdec_reg_forwards (sailRegister rd) ++
          0b0110011#7 := by
  simp [generatedRtypeEncodingWithFields]
  bv_decide

@[simp] theorem generatedRtypeEncodingWithFields_low12 (funct7 : BitVec 7)
    (rs2 rs1 rd : RV32I.Register) (funct3 : BitVec 3) :
    Sail.BitVec.extractLsb
        (generatedRtypeEncodingWithFields funct7 rs2 rs1 rd funct3) 11 0 =
      encdec_reg_forwards (sailRegister rd) ++ 0b0110011#7 := by
  simp [generatedRtypeEncodingWithFields, Sail.BitVec.extractLsb]
  bv_decide

@[simp] theorem generatedRtypeEncodingWithFields_low12_core (funct7 : BitVec 7)
    (rs2 rs1 rd : RV32I.Register) (funct3 : BitVec 3) :
    (generatedRtypeEncodingWithFields funct7 rs2 rs1 rd funct3).extractLsb'
        0 12 = encdec_reg_forwards (sailRegister rd) ++ 0b0110011#7 := by
  simp [generatedRtypeEncodingWithFields]
  bv_decide

@[simp] theorem generatedRtypeEncoding_ne_pause (rs2 rs1 rd : RV32I.Register)
    (operation : LeanRV32D.rop) :
    generatedRtypeEncoding rs2 rs1 rd operation ≠ 0x0100000f := by
  intro equal
  have := congrArg (fun word => Sail.BitVec.extractLsb word 6 0) equal
  simp [generatedRtypeEncoding] at this
  have concrete : Sail.BitVec.extractLsb (0x0100000f#32) 6 0 = 0b0001111#7 := by
    native_decide
  rw [concrete] at this
  clear equal rs2 rs1 rd operation
  bv_decide

theorem generatedRtype_pause_guard_false (rs2 rs1 rd : RV32I.Register)
    (operation : LeanRV32D.rop) :
    ¬ ((generatedRtypeEncoding rs2 rs1 rd operation == 0x0100000f) = true) := by
  simpa only [beq_iff_eq] using
    generatedRtypeEncoding_ne_pause rs2 rs1 rd operation

@[simp] theorem generatedRtypeEncodingWithFields_ne_pause (funct7 : BitVec 7)
    (rs2 rs1 rd : RV32I.Register) (funct3 : BitVec 3) :
    generatedRtypeEncodingWithFields funct7 rs2 rs1 rd funct3 ≠
      0x0100000f := by
  intro equal
  have extracted := congrArg (fun word => Sail.BitVec.extractLsb word 6 0) equal
  simp at extracted
  have concrete : Sail.BitVec.extractLsb (0x0100000f#32) 6 0 = 0b0001111#7 := by
    native_decide
  rw [concrete] at extracted
  clear equal funct7 rs2 rs1 rd funct3
  bv_decide

@[simp] theorem generatedRtypeEncoding_rs2_core (rs2 rs1 rd : RV32I.Register)
    (operation : LeanRV32D.rop) :
    (generatedRtypeEncoding rs2 rs1 rd operation).extractLsb' 20 5 =
      encdec_reg_forwards (sailRegister rs2) := by
  simp [generatedRtypeEncoding]

@[simp] theorem generatedRtypeEncoding_funct7 (rs2 rs1 rd : RV32I.Register)
    (operation : LeanRV32D.rop) :
    Sail.BitVec.extractLsb (generatedRtypeEncoding rs2 rs1 rd operation) 31 25 =
      generatedRtypeFunct7 operation := by simp [generatedRtypeEncoding]

@[simp] theorem generatedRtypeEncoding_funct7_core (rs2 rs1 rd : RV32I.Register)
    (operation : LeanRV32D.rop) :
    (generatedRtypeEncoding rs2 rs1 rd operation).extractLsb' 25 7 =
      generatedRtypeFunct7 operation := by
  simp [generatedRtypeEncoding, generatedRtypeEncodingWithFields]
  bv_decide

@[simp] theorem generatedRtypeEncoding_rs2 (rs2 rs1 rd : RV32I.Register)
    (operation : LeanRV32D.rop) :
    Sail.BitVec.extractLsb (generatedRtypeEncoding rs2 rs1 rd operation) 24 20 =
      encdec_reg_forwards (sailRegister rs2) := by simp [generatedRtypeEncoding]

@[simp] theorem generatedRtypeEncoding_rs1 (rs2 rs1 rd : RV32I.Register)
    (operation : LeanRV32D.rop) :
    Sail.BitVec.extractLsb (generatedRtypeEncoding rs2 rs1 rd operation) 19 15 =
      encdec_reg_forwards (sailRegister rs1) := by simp [generatedRtypeEncoding]

@[simp] theorem generatedRtypeEncoding_funct3 (rs2 rs1 rd : RV32I.Register)
    (operation : LeanRV32D.rop) :
    Sail.BitVec.extractLsb (generatedRtypeEncoding rs2 rs1 rd operation) 14 12 =
      generatedRtypeFunct3 operation := by simp [generatedRtypeEncoding]

@[simp] theorem generatedRtypeEncoding_rd (rs2 rs1 rd : RV32I.Register)
    (operation : LeanRV32D.rop) :
    Sail.BitVec.extractLsb (generatedRtypeEncoding rs2 rs1 rd operation) 11 7 =
      encdec_reg_forwards (sailRegister rd) := by simp [generatedRtypeEncoding]

@[simp] theorem generatedRtypeEncoding_opcode (rs2 rs1 rd : RV32I.Register)
    (operation : LeanRV32D.rop) :
    Sail.BitVec.extractLsb (generatedRtypeEncoding rs2 rs1 rd operation) 6 0 =
      0b0110011#7 := by simp [generatedRtypeEncoding]

@[simp] theorem generatedRtypeEncoding_opcode_core (rs2 rs1 rd : RV32I.Register)
    (operation : LeanRV32D.rop) :
    (generatedRtypeEncoding rs2 rs1 rd operation).extractLsb' 0 7 =
      0b0110011#7 := by simp [generatedRtypeEncoding]

@[simp] theorem generatedRtypeEncoding_opcode_beq_core
    (rs2 rs1 rd : RV32I.Register) (operation : LeanRV32D.rop)
    (candidate : BitVec 7) :
    ((generatedRtypeEncoding rs2 rs1 rd operation).extractLsb' 0 7 ==
        candidate) = (0b0110011#7 == candidate) := by
  rw [generatedRtypeEncoding_opcode_core]

@[simp] theorem generatedRtype_uop_matcher_false
    (rs2 rs1 rd : RV32I.Register) (operation : LeanRV32D.rop) :
    encdec_uop_backwards_matches
      ((generatedRtypeEncoding rs2 rs1 rd operation).extractLsb' 0 7) = false := by
  rw [generatedRtypeEncoding_opcode_core]
  rfl

@[simp] theorem generatedRtype_uop_match_false
    (rs2 rs1 rd : RV32I.Register) (operation : LeanRV32D.rop) :
    (match (generatedRtypeEncoding rs2 rs1 rd operation).extractLsb' 0 7 with
      | 0b0110111 => true
      | 0b0010111 => true
      | _ => false) = false := by
  rw [generatedRtypeEncoding_opcode_core]
  native_decide

theorem generatedRtype_utype_guard_false
    (rs2 rs1 rd : RV32I.Register) (operation : LeanRV32D.rop) :
    ¬ ((match (generatedRtypeEncoding rs2 rs1 rd operation).extractLsb' 0 7 with
      | 0b0110111 => true
      | 0b0010111 => true
      | _ => false) = true) := by
  rw [generatedRtype_uop_match_false]
  decide

private theorem rtypeBoolAndLeft {left right : Bool}
    (both : (left && right) = true) : left = true := by
  cases left <;> cases right <;> simp_all

theorem generatedRtype_utype_clause_guard_false
    (rs2 rs1 rd : RV32I.Register) (operation : LeanRV32D.rop) :
    ¬ ((encdec_uop_backwards_matches
          (Sail.BitVec.extractLsb
            (generatedRtypeEncoding rs2 rs1 rd operation) 6 0) &&
        encdec_reg_backwards_matches
          (Sail.BitVec.extractLsb
            (generatedRtypeEncoding rs2 rs1 rd operation) 11 7)) = true) := by
  intro guard
  have opcodeMatches : encdec_uop_backwards_matches
      (Sail.BitVec.extractLsb
        (generatedRtypeEncoding rs2 rs1 rd operation) 6 0) = true := by
    exact rtypeBoolAndLeft guard
  simp [generatedRtypeEncoding_opcode, encdec_uop_backwards_matches] at opcodeMatches

@[simp] theorem generatedRtypeEncoding_low20 (rs2 rs1 rd : RV32I.Register)
    (operation : LeanRV32D.rop) :
    Sail.BitVec.extractLsb (generatedRtypeEncoding rs2 rs1 rd operation) 19 0 =
      encdec_reg_forwards (sailRegister rs1) ++
        generatedRtypeFunct3 operation ++
        encdec_reg_forwards (sailRegister rd) ++ 0b0110011#7 := by
  simp [generatedRtypeEncoding]

@[simp] theorem generatedRtypeEncoding_low20_core (rs2 rs1 rd : RV32I.Register)
    (operation : LeanRV32D.rop) :
    (generatedRtypeEncoding rs2 rs1 rd operation).extractLsb' 0 20 =
      encdec_reg_forwards (sailRegister rs1) ++
        generatedRtypeFunct3 operation ++
        encdec_reg_forwards (sailRegister rd) ++ 0b0110011#7 := by
  simp [generatedRtypeEncoding, generatedRtypeEncodingWithFields]
  bv_decide

@[simp] theorem generatedRtypeEncoding_low15 (rs2 rs1 rd : RV32I.Register)
    (operation : LeanRV32D.rop) :
    Sail.BitVec.extractLsb (generatedRtypeEncoding rs2 rs1 rd operation) 14 0 =
      generatedRtypeFunct3 operation ++
        encdec_reg_forwards (sailRegister rd) ++ 0b0110011#7 := by
  simp [generatedRtypeEncoding]

@[simp] theorem generatedRtypeEncoding_low15_core (rs2 rs1 rd : RV32I.Register)
    (operation : LeanRV32D.rop) :
    (generatedRtypeEncoding rs2 rs1 rd operation).extractLsb' 0 15 =
      generatedRtypeFunct3 operation ++
        encdec_reg_forwards (sailRegister rd) ++ 0b0110011#7 := by
  simp [generatedRtypeEncoding, generatedRtypeEncodingWithFields]
  bv_decide

@[simp] theorem generatedRtypeEncoding_low12 (rs2 rs1 rd : RV32I.Register)
    (operation : LeanRV32D.rop) :
    Sail.BitVec.extractLsb (generatedRtypeEncoding rs2 rs1 rd operation) 11 0 =
      encdec_reg_forwards (sailRegister rd) ++ 0b0110011#7 := by
  simp [generatedRtypeEncoding]

@[simp] theorem generatedRtypeEncoding_low12_core (rs2 rs1 rd : RV32I.Register)
    (operation : LeanRV32D.rop) :
    (generatedRtypeEncoding rs2 rs1 rd operation).extractLsb' 0 12 =
      encdec_reg_forwards (sailRegister rd) ++ 0b0110011#7 := by
  simp [generatedRtypeEncoding, generatedRtypeEncodingWithFields]
  bv_decide

@[simp] theorem generatedRtypeOperandDecode_encoding (rs2 rs1 rd : RV32I.Register)
    (operation : LeanRV32D.rop) (sail : SailState) :
    generatedRtypeOperandDecode
        (generatedRtypeEncoding rs2 rs1 rd operation) operation sail =
      .ok (some (.RTYPE (sailRegister rs2, sailRegister rs1,
        sailRegister rd, operation))) sail := by
  simp [generatedRtypeOperandDecode, generatedRtypeEncoding,
    bind, EStateM.bind, pure, EStateM.pure]

@[simp] theorem clean_decodes_generatedRtypeEncoding (rs2 rs1 rd : RV32I.Register)
    (operation : LeanRV32D.rop) :
    RV32I.Decoder.decode (generatedRtypeEncoding rs2 rs1 rd operation) =
      some (cleanRtypeInstruction operation rd rs1 rs2) := by
  have hopcode : RV32I.Decoder.opcode
      (generatedRtypeEncoding rs2 rs1 rd operation) = 0b0110011#7 := by
    simp [RV32I.Decoder.opcode, generatedRtypeEncoding,
      generatedRtypeEncodingWithFields]
    bv_decide
  have hfunct3 : RV32I.Decoder.funct3
      (generatedRtypeEncoding rs2 rs1 rd operation) =
        generatedRtypeFunct3 operation := by
    simp [RV32I.Decoder.funct3, generatedRtypeEncoding,
      generatedRtypeEncodingWithFields]
    bv_decide
  have hfunct7 : RV32I.Decoder.funct7
      (generatedRtypeEncoding rs2 rs1 rd operation) =
        generatedRtypeFunct7 operation := by
    simp [RV32I.Decoder.funct7, generatedRtypeEncoding,
      generatedRtypeEncodingWithFields]
    bv_decide
  have hrd : RV32I.Decoder.rd
      (generatedRtypeEncoding rs2 rs1 rd operation) = rd := by
    have bits :
        (generatedRtypeEncoding rs2 rs1 rd operation).extractLsb' 7 5 =
          BitVec.ofNat 5 rd.val := by
      simp [generatedRtypeEncoding, generatedRtypeEncodingWithFields,
        encdec_reg_forwards, sailRegister, LeanRV32D.zero_extend,
        Sail.BitVec.zeroExtend]
      bv_decide
    simp [RV32I.Decoder.rd, bits]
  have hrs1 : RV32I.Decoder.rs1
      (generatedRtypeEncoding rs2 rs1 rd operation) = rs1 := by
    have bits :
        (generatedRtypeEncoding rs2 rs1 rd operation).extractLsb' 15 5 =
          BitVec.ofNat 5 rs1.val := by
      simp [generatedRtypeEncoding, generatedRtypeEncodingWithFields,
        encdec_reg_forwards, sailRegister, LeanRV32D.zero_extend,
        Sail.BitVec.zeroExtend]
      bv_decide
    simp [RV32I.Decoder.rs1, bits]
  have hrs2 : RV32I.Decoder.rs2
      (generatedRtypeEncoding rs2 rs1 rd operation) = rs2 := by
    have bits :
        (generatedRtypeEncoding rs2 rs1 rd operation).extractLsb' 20 5 =
          BitVec.ofNat 5 rs2.val := by
      simp [generatedRtypeEncoding, generatedRtypeEncodingWithFields,
        encdec_reg_forwards, sailRegister, LeanRV32D.zero_extend,
        Sail.BitVec.zeroExtend]
      bv_decide
    simp [RV32I.Decoder.rs2, bits]
  cases operation <;>
    simp only [generatedRtypeFunct3, generatedRtypeFunct7,
      cleanRtypeInstruction] at hfunct3 hfunct7 ⊢ <;>
    simp [RV32I.Decoder.decode, hopcode, hfunct3, hfunct7, hrd, hrs1, hrs2]

/-- Exactly the four base ADD HINT words intercepted by the generated
platform's hard-enabled Zihintntl clause. -/
abbrev NtlInterposes (rs2 rs1 rd : RV32I.Register) : Prop :=
  let word := generatedRtypeEncoding rs2 rs1 rd .ADD
  ((encdec_ntl_backwards_matches (Sail.BitVec.extractLsb word 24 20) &&
      ((Sail.BitVec.extractLsb word 31 25 == 0b0000000#7) &&
        (Sail.BitVec.extractLsb word 19 0 == 0x00033#20))) = true)

def generatedNtlEncoding (operation : LeanRV32D.ntl_type) : RV32I.Word :=
  0b0000000#7 ++ encdec_ntl_forwards operation ++ 0b00000#5 ++
    0b000#3 ++ 0b00000#5 ++ 0b0110011#7

@[simp] theorem generatedNtlEncoding_eq (operation : LeanRV32D.ntl_type) :
    generatedNtlEncoding operation =
      0b0000000#7 ++ encdec_ntl_forwards operation ++ 0b00000#5 ++
        0b000#3 ++ 0b00000#5 ++ 0b0110011#7 := by
  cases operation <;> rfl

theorem generatedNtl_guard_true (operation : LeanRV32D.ntl_type) :
    ((encdec_ntl_backwards_matches
          (Sail.BitVec.extractLsb (generatedNtlEncoding operation) 24 20) &&
        ((Sail.BitVec.extractLsb (generatedNtlEncoding operation) 31 25 ==
            0b0000000#7) &&
          (Sail.BitVec.extractLsb (generatedNtlEncoding operation) 19 0 ==
            0x00033#20))) = true) := by
  cases operation <;>
    simp [generatedNtlEncoding, encdec_ntl_forwards,
      encdec_ntl_backwards_matches, Sail.BitVec.extractLsb] <;>
    bv_decide

theorem ntlInterposes_characterization :
    ∀ rs2 rs1 rd : RV32I.Register,
      NtlInterposes rs2 rs1 rd ↔
        rs1 = 0 ∧ rd = 0 ∧
          (rs2 = 2 ∨ rs2 = 3 ∨ rs2 = 4 ∨ rs2 = 5) := by
  unfold NtlInterposes generatedRtypeEncoding generatedRtypeEncodingWithFields
    generatedRtypeFunct7 generatedRtypeFunct3
  native_decide

theorem generatedRtype_ntl_guard_characterization
    (rs2 rs1 rd : RV32I.Register) (operation : LeanRV32D.rop) :
    ((encdec_ntl_backwards_matches
          (Sail.BitVec.extractLsb
            (generatedRtypeEncoding rs2 rs1 rd operation) 24 20) &&
        ((Sail.BitVec.extractLsb
              (generatedRtypeEncoding rs2 rs1 rd operation) 31 25 ==
            0b0000000#7) &&
          (Sail.BitVec.extractLsb
              (generatedRtypeEncoding rs2 rs1 rd operation) 19 0 ==
            0x00033#20))) = true) ↔
      operation = .ADD ∧ NtlInterposes rs2 rs1 rd := by
  cases operation
  · constructor
    · intro interposes
      exact ⟨rfl, interposes⟩
    · intro interposes
      exact interposes.2
  all_goals
    simp [NtlInterposes, generatedRtypeEncoding,
      generatedRtypeEncodingWithFields, generatedRtypeFunct7,
      generatedRtypeFunct3, encdec_reg_forwards, sailRegister,
      LeanRV32D.zero_extend, Sail.BitVec.zeroExtend,
      Sail.BitVec.extractLsb]
  all_goals bv_decide

theorem generatedRtype_ntl_guard_false (rs2 rs1 rd : RV32I.Register)
    (operation : LeanRV32D.rop) (notAdd : operation ≠ .ADD) :
    ¬ ((encdec_ntl_backwards_matches
          (Sail.BitVec.extractLsb
            (generatedRtypeEncoding rs2 rs1 rd operation) 24 20) &&
        ((Sail.BitVec.extractLsb
              (generatedRtypeEncoding rs2 rs1 rd operation) 31 25 ==
            0b0000000#7) &&
          (Sail.BitVec.extractLsb
              (generatedRtypeEncoding rs2 rs1 rd operation) 19 0 ==
            0x00033#20))) = true) := by
  intro interposes
  exact notAdd
    ((generatedRtype_ntl_guard_characterization rs2 rs1 rd operation).mp
      interposes).1

private theorem boolAndRight {left right : Bool}
    (both : (left && right) = true) : right = true := by
  cases left <;> cases right <;> simp_all

private theorem boolAndLeft {left right : Bool}
    (both : (left && right) = true) : left = true := by
  cases left <;> cases right <;> simp_all

private theorem boolAndBeqRight {α : Type} [BEq α] [LawfulBEq α]
    {left : Bool} {x y : α} (both : (left && (x == y)) = true) : x = y := by
  cases hleft : left <;> simp_all

theorem generatedRtype_zicbop_guard_false (rs2 rs1 rd : RV32I.Register)
    (operation : LeanRV32D.rop) :
    ¬ ((((encdec_cbop_zicbop_backwards_matches
            (Sail.BitVec.extractLsb
              (generatedRtypeEncoding rs2 rs1 rd operation) 24 20)) &&
          encdec_reg_backwards_matches
            (Sail.BitVec.extractLsb
              (generatedRtypeEncoding rs2 rs1 rd operation) 19 15)) &&
        (Sail.BitVec.extractLsb
            (generatedRtypeEncoding rs2 rs1 rd operation) 14 0 ==
          0b110000000010011#15)) = true) := by
  intro guard
  have low : Sail.BitVec.extractLsb
      (generatedRtypeEncoding rs2 rs1 rd operation) 14 0 =
        0b110000000010011#15 := boolAndBeqRight guard
  have opcodeMismatch := congrArg (fun bits : BitVec 15 => bits.extractLsb' 0 7)
    low
  simp [generatedRtypeEncoding_low15, encdec_reg_forwards, sailRegister,
    LeanRV32D.zero_extend, Sail.BitVec.zeroExtend] at opcodeMismatch
  clear guard low rs2 rs1
  cases operation <;> simp_all [generatedRtypeFunct3]
  all_goals bv_decide

def GeneratedRtypeClauseGuard (word : RV32I.Word)
    (funct7 : BitVec 7) (funct3 : BitVec 3) : Prop :=
  (((encdec_reg_backwards_matches (Sail.BitVec.extractLsb word 24 20) &&
        (encdec_reg_backwards_matches (Sail.BitVec.extractLsb word 19 15) &&
          encdec_reg_backwards_matches (Sail.BitVec.extractLsb word 11 7))) &&
      ((Sail.BitVec.extractLsb word 31 25 == funct7) &&
        ((Sail.BitVec.extractLsb word 14 12 == funct3) &&
          (Sail.BitVec.extractLsb word 6 0 == 0b0110011#7)))) = true)

theorem generatedRtype_clause_guard_iff (rs2 rs1 rd : RV32I.Register)
    (wordOperation clauseOperation : LeanRV32D.rop) :
    GeneratedRtypeClauseGuard
        (generatedRtypeEncoding rs2 rs1 rd wordOperation)
        (generatedRtypeFunct7 clauseOperation)
        (generatedRtypeFunct3 clauseOperation) ↔
      wordOperation = clauseOperation := by
  cases wordOperation <;> cases clauseOperation <;>
    simp [GeneratedRtypeClauseGuard, generatedRtypeEncoding,
      generatedRtypeEncodingWithFields, generatedRtypeFunct7,
      generatedRtypeFunct3, encdec_reg_forwards, sailRegister,
      LeanRV32D.zero_extend, Sail.BitVec.zeroExtend,
      Sail.BitVec.extractLsb] <;>
    bv_decide

theorem generatedRtype_clause_guard_true (rs2 rs1 rd : RV32I.Register)
    (wordOperation clauseOperation : LeanRV32D.rop)
    (same : wordOperation = clauseOperation) :
    GeneratedRtypeClauseGuard
      (generatedRtypeEncoding rs2 rs1 rd wordOperation)
      (generatedRtypeFunct7 clauseOperation)
      (generatedRtypeFunct3 clauseOperation) :=
  (generatedRtype_clause_guard_iff rs2 rs1 rd wordOperation clauseOperation).2 same

theorem generatedRtype_clause_guard_false (rs2 rs1 rd : RV32I.Register)
    (wordOperation clauseOperation : LeanRV32D.rop)
    (different : wordOperation ≠ clauseOperation) :
    ¬ GeneratedRtypeClauseGuard
      (generatedRtypeEncoding rs2 rs1 rd wordOperation)
      (generatedRtypeFunct7 clauseOperation)
      (generatedRtypeFunct3 clauseOperation) := fun guard =>
  different
    ((generatedRtype_clause_guard_iff rs2 rs1 rd wordOperation clauseOperation).1
      guard)

/-- The generated NTL clause's operand decoder. -/
def generatedNtlOperandDecode (word : RV32I.Word) :
    LeanRV32D.SailM (Option LeanRV32D.instruction) := do
  let operation ← encdec_ntl_backwards (Sail.BitVec.extractLsb word 24 20)
  pure (some (.NTL operation))

@[simp] theorem generatedNtlOperandDecode_encoding
    (operation : LeanRV32D.ntl_type) (sail : SailState) :
    generatedNtlOperandDecode (generatedNtlEncoding operation) sail =
      .ok (some (.NTL operation)) sail := by
  have bits : Sail.BitVec.extractLsb (generatedNtlEncoding operation) 24 20 =
      encdec_ntl_forwards operation := by
    simp [generatedNtlEncoding, Sail.BitVec.extractLsb]
    bv_decide
  change (do
      let decoded ← encdec_ntl_backwards
        (Sail.BitVec.extractLsb (generatedNtlEncoding operation) 24 20)
      pure (some (LeanRV32D.instruction.NTL decoded))) sail = _
  rw [bits]
  simp [bind, EStateM.bind, pure, EStateM.pure]

private def zeroRegister : RV32I.Register := 0

private def ntlSource : LeanRV32D.ntl_type → RV32I.Register
  | .NTL_P1 => 2
  | .NTL_PALL => 3
  | .NTL_S1 => 4
  | .NTL_ALL => 5

/-- Interpret a generated instruction as a base-RV32I decoded instruction
when it has such an interpretation.

`NTL` and `PAUSE` are included because the generated platform enables those
standard HINT extensions unconditionally and their encodings retain valid
base-RV32I HINT interpretations.  Landing pads are intentionally absent: when
Zicfilp is active their execution is not merely the base AUIPC-to-x0 HINT, so
the decoder theorem must state that Zicfilp interposition is disabled. -/
def generatedBaseView : LeanRV32D.instruction → Option RV32I.DecodedInstruction
  | .ZICBOP (operation, rs1, offset) =>
      some (.ori 0 (cleanRegister rs1)
        (offset.extractLsb' 5 7 ++ encdec_cbop_zicbop_forwards operation))
  | .NTL operation =>
      some (.add zeroRegister zeroRegister (ntlSource operation))
  | .PAUSE () =>
      some (.fence (.normal (RV32I.FenceSet.ofBits 0b0001#4)
        (RV32I.FenceSet.ofBits 0b0000#4)))
  | .UTYPE (immediate, rd, .LUI) =>
      some (.lui (cleanRegister rd) immediate)
  | .UTYPE (immediate, rd, .AUIPC) =>
      some (.auipc (cleanRegister rd) immediate)
  | .JAL (immediate, rd) =>
      some (.jal (cleanRegister rd) immediate)
  | .JALR (immediate, rs1, rd) =>
      some (.jalr (cleanRegister rd) (cleanRegister rs1) immediate)
  | .BTYPE (immediate, rs2, rs1, .BEQ) =>
      some (.beq (cleanRegister rs1) (cleanRegister rs2) immediate)
  | .BTYPE (immediate, rs2, rs1, .BNE) =>
      some (.bne (cleanRegister rs1) (cleanRegister rs2) immediate)
  | .BTYPE (immediate, rs2, rs1, .BLT) =>
      some (.blt (cleanRegister rs1) (cleanRegister rs2) immediate)
  | .BTYPE (immediate, rs2, rs1, .BGE) =>
      some (.bge (cleanRegister rs1) (cleanRegister rs2) immediate)
  | .BTYPE (immediate, rs2, rs1, .BLTU) =>
      some (.bltu (cleanRegister rs1) (cleanRegister rs2) immediate)
  | .BTYPE (immediate, rs2, rs1, .BGEU) =>
      some (.bgeu (cleanRegister rs1) (cleanRegister rs2) immediate)
  | .ITYPE (immediate, rs1, rd, .ADDI) =>
      some (.addi (cleanRegister rd) (cleanRegister rs1) immediate)
  | .ITYPE (immediate, rs1, rd, .SLTI) =>
      some (.slti (cleanRegister rd) (cleanRegister rs1) immediate)
  | .ITYPE (immediate, rs1, rd, .SLTIU) =>
      some (.sltiu (cleanRegister rd) (cleanRegister rs1) immediate)
  | .ITYPE (immediate, rs1, rd, .XORI) =>
      some (.xori (cleanRegister rd) (cleanRegister rs1) immediate)
  | .ITYPE (immediate, rs1, rd, .ORI) =>
      some (.ori (cleanRegister rd) (cleanRegister rs1) immediate)
  | .ITYPE (immediate, rs1, rd, .ANDI) =>
      some (.andi (cleanRegister rd) (cleanRegister rs1) immediate)
  | .SHIFTIOP (shamt, rs1, rd, operation) =>
      if shamt.toNat < 32 then
        let amount : BitVec 5 := shamt.truncate 5
        match operation with
        | .SLLI => some (.slli (cleanRegister rd) (cleanRegister rs1) amount)
        | .SRLI => some (.srli (cleanRegister rd) (cleanRegister rs1) amount)
        | .SRAI => some (.srai (cleanRegister rd) (cleanRegister rs1) amount)
      else none
  | .RTYPE (rs2, rs1, rd, .ADD) =>
      some (.add (cleanRegister rd) (cleanRegister rs1) (cleanRegister rs2))
  | .RTYPE (rs2, rs1, rd, .SUB) =>
      some (.sub (cleanRegister rd) (cleanRegister rs1) (cleanRegister rs2))
  | .RTYPE (rs2, rs1, rd, .SLL) =>
      some (.sll (cleanRegister rd) (cleanRegister rs1) (cleanRegister rs2))
  | .RTYPE (rs2, rs1, rd, .SLT) =>
      some (.slt (cleanRegister rd) (cleanRegister rs1) (cleanRegister rs2))
  | .RTYPE (rs2, rs1, rd, .SLTU) =>
      some (.sltu (cleanRegister rd) (cleanRegister rs1) (cleanRegister rs2))
  | .RTYPE (rs2, rs1, rd, .XOR) =>
      some (.xor (cleanRegister rd) (cleanRegister rs1) (cleanRegister rs2))
  | .RTYPE (rs2, rs1, rd, .SRL) =>
      some (.srl (cleanRegister rd) (cleanRegister rs1) (cleanRegister rs2))
  | .RTYPE (rs2, rs1, rd, .SRA) =>
      some (.sra (cleanRegister rd) (cleanRegister rs1) (cleanRegister rs2))
  | .RTYPE (rs2, rs1, rd, .OR) =>
      some (.or (cleanRegister rd) (cleanRegister rs1) (cleanRegister rs2))
  | .RTYPE (rs2, rs1, rd, .AND) =>
      some (.and (cleanRegister rd) (cleanRegister rs1) (cleanRegister rs2))
  | .LOAD (immediate, rs1, rd, false, 1) =>
      some (.lb (cleanRegister rd) (cleanRegister rs1) immediate)
  | .LOAD (immediate, rs1, rd, false, 2) =>
      some (.lh (cleanRegister rd) (cleanRegister rs1) immediate)
  | .LOAD (immediate, rs1, rd, false, 4) =>
      some (.lw (cleanRegister rd) (cleanRegister rs1) immediate)
  | .LOAD (immediate, rs1, rd, true, 1) =>
      some (.lbu (cleanRegister rd) (cleanRegister rs1) immediate)
  | .LOAD (immediate, rs1, rd, true, 2) =>
      some (.lhu (cleanRegister rd) (cleanRegister rs1) immediate)
  | .STORE (immediate, rs2, rs1, 1) =>
      some (.sb (cleanRegister rs2) (cleanRegister rs1) immediate)
  | .STORE (immediate, rs2, rs1, 2) =>
      some (.sh (cleanRegister rs2) (cleanRegister rs1) immediate)
  | .STORE (immediate, rs2, rs1, 4) =>
      some (.sw (cleanRegister rs2) (cleanRegister rs1) immediate)
  | .FENCE_TSO () => some (.fence .tso)
  | .FENCE (_, predecessor, successor, _, _) =>
      some (.fence (.normal (RV32I.FenceSet.ofBits predecessor)
        (RV32I.FenceSet.ofBits successor)))
  | .ECALL () => some .ecall
  | .EBREAK () => some .ebreak
  | _ => none

/-- The non-base categories needed to explain a word rejected by the clean
decoder. `otherExtension` intentionally collects the generated model's large
and evolving extension surface without copying it into this bridge API. -/
inductive ExcludedGeneratedInstructionClass where
  | illegal
  | privileged
  | csrOrCounter
  | zifencei
  | otherExtension
  deriving DecidableEq, Repr

inductive GeneratedInstructionClass where
  | base
  | excluded (reason : ExcludedGeneratedInstructionClass)
  deriving DecidableEq, Repr

private def excludedInstructionClass :
    LeanRV32D.instruction → ExcludedGeneratedInstructionClass
  | .ILLEGAL _ => .illegal
  | .MRET () | .SRET () | .WFI () | .SFENCE_VMA _ => .privileged
  | .CSRReg _ | .CSRImm _ => .csrOrCounter
  | .FENCEI _ => .zifencei
  | _ => .otherExtension

def generatedInstructionClass
    (instruction : LeanRV32D.instruction) : GeneratedInstructionClass :=
  if generatedBaseView instruction |>.isSome then
    .base
  else .excluded (excludedInstructionClass instruction)

theorem generatedInstructionClass_base_iff (instruction : LeanRV32D.instruction) :
    generatedInstructionClass instruction = .base ↔
      ∃ decoded, generatedBaseView instruction = some decoded := by
  simp [generatedInstructionClass, Option.isSome_iff_exists]

/-- Pointwise decoder agreement after the generated monad has produced an
instruction.  Keeping this predicate separate prevents clients from unfolding
the generated decoder's enormous mapping by accident. -/
def DecodersCorrespondAt (word : RV32I.Word)
    (generated : LeanRV32D.instruction) : Prop :=
  generatedBaseView generated = RV32I.Decoder.decode word

theorem clean_legal_of_decoder_correspondence
    {word : RV32I.Word} {generated : LeanRV32D.instruction}
    {decoded : RV32I.DecodedInstruction}
    (corresponds : DecodersCorrespondAt word generated)
    (cleanLegal : RV32I.Decoder.decode word = some decoded) :
    generatedBaseView generated = some decoded := by
  rw [corresponds, cleanLegal]

theorem clean_rejected_classified_nonbase
    {word : RV32I.Word} {generated : LeanRV32D.instruction}
    (corresponds : DecodersCorrespondAt word generated)
    (cleanRejected : RV32I.Decoder.decode word = none) :
    ∃ reason, generatedInstructionClass generated = .excluded reason := by
  have viewNone : generatedBaseView generated = none := by
    rw [corresponds, cleanRejected]
  refine ⟨excludedInstructionClass generated, ?_⟩
  simp [generatedInstructionClass, viewNone]

end RV32I.SailBridge
