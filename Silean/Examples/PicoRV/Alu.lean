import Silean.Foundation.BitVector
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModulePorts
import Silean.Contracts.Cycle.CycleContract
import Silean.Contracts.Cycle.CycleEvaluation
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Modules.AddSub.AddSubCertified
import Silean.Modules.BitwiseAnd
import Silean.Modules.BitwiseOr
import Silean.Modules.BitwiseXor
import Silean.Modules.Constant
import Silean.Modules.Equality
import Silean.Modules.Mux.Mux
import Silean.Modules.Mux.MuxCertified
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming
import Silean.Primitives.Not
import Silean.Primitives.Or
import Silean.Primitives.Xor

namespace Silean.Examples.PicoRV.Alu

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

/-! Contract and certified concrete structure for the combinational PicoRV32
ALU. The boundary names and operation-selection behavior follow the target
Verilog configuration. -/

abbrev Word := Fin 32 → Bool

module_ports ports where
  input reg_op1 : .vector 32 .bit,
  input reg_op2 : .vector 32 .bit,
  input instr_sub : .bit,
  input instr_beq : .bit,
  input instr_bne : .bit,
  input instr_bge : .bit,
  input instr_bgeu : .bit,
  input is_slti_blt_slt : .bit,
  input is_sltiu_bltu_sltu : .bit,
  input is_lui_auipc_jal_jalr_addi_add_sub : .bit,
  input is_compare : .bit,
  input instr_xori : .bit,
  input instr_xor : .bit,
  input instr_ori : .bit,
  input instr_or : .bit,
  input instr_andi : .bit,
  input instr_and : .bit,
  output alu_out : .vector 32 .bit,
  output alu_out_0 : .bit

def wordOfNat (value : Nat) : Word := BitVector.ofNat 32 value

def wordOfBool (value : Bool) : Word := fun index =>
  if index = 0 then value else false

def addSub (instr_sub : Bool) (reg_op1 reg_op2 : Word) : Word :=
  let modulus := BitVector.cardinality 32
  let left := BitVector.toNat 32 reg_op1
  let right := BitVector.toNat 32 reg_op2
  if instr_sub then wordOfNat ((left + modulus - right) % modulus)
  else wordOfNat ((left + right) % modulus)

def equal (reg_op1 reg_op2 : Word) : Bool :=
  decide (BitVector.toNat 32 reg_op1 = BitVector.toNat 32 reg_op2)

private theorem equal_eq_signalEqual (left right : Word) :
    equal left right = (SignalType.vector 32 .bit).equal left right := by
  apply Bool.eq_iff_iff.mpr
  rw [SignalType.equal_eq_true_iff]
  simp only [equal, decide_eq_true_eq]
  constructor
  · exact fun equality => (BitVector.toNat_injective 32) equality
  · exact congrArg (BitVector.toNat 32)

def unsignedLessThan (reg_op1 reg_op2 : Word) : Bool :=
  decide (BitVector.toNat 32 reg_op1 < BitVector.toNat 32 reg_op2)

def signedLessThan (reg_op1 reg_op2 : Word) : Bool :=
  if reg_op1 31 = reg_op2 31 then unsignedLessThan reg_op1 reg_op2
  else reg_op1 31

def bitwiseXor (reg_op1 reg_op2 : Word) : Word :=
  fun index => Bool.xor (reg_op1 index) (reg_op2 index)

def bitwiseOr (reg_op1 reg_op2 : Word) : Word :=
  fun index => reg_op1 index || reg_op2 index

def bitwiseAnd (reg_op1 reg_op2 : Word) : Word :=
  fun index => reg_op1 index && reg_op2 index

structure Values where
  reg_op1 : Word
  reg_op2 : Word
  instr_sub : Bool
  instr_beq : Bool
  instr_bne : Bool
  instr_bge : Bool
  instr_bgeu : Bool
  is_slti_blt_slt : Bool
  is_sltiu_bltu_sltu : Bool
  is_lui_auipc_jal_jalr_addi_add_sub : Bool
  is_compare : Bool
  instr_xori : Bool
  instr_xor : Bool
  instr_ori : Bool
  instr_or : Bool
  instr_andi : Bool
  instr_and : Bool

inductive Comparison
  | equal
  | notEqual
  | signedGreaterOrEqual
  | unsignedGreaterOrEqual
  | signedLessThan
  | unsignedLessThan

inductive Operation
  | zero
  | add
  | subtract
  | compare
  | bitwiseXor
  | bitwiseOr
  | bitwiseAnd

structure Result where
  alu_out : Word
  alu_out_0 : Bool

def selectedComparison (inputs : Values) : Comparison :=
  bif inputs.instr_beq then .equal
  else bif inputs.instr_bne then .notEqual
  else bif inputs.instr_bge then .signedGreaterOrEqual
  else bif inputs.instr_bgeu then .unsignedGreaterOrEqual
  else bif inputs.is_slti_blt_slt then .signedLessThan
  else bif inputs.is_sltiu_bltu_sltu then .unsignedLessThan
  else .equal

def selectedOperation (inputs : Values) : Operation :=
  /- On decoder-valid inputs, `is_compare` and the arithmetic result class are
  disjoint. Including it here exposes the mode of the one shared AddSub for a
  total contract without adding impossible-control detection hardware. -/
  let arithmetic := bif inputs.instr_sub || inputs.is_compare then
    Operation.subtract else .add
  bif inputs.is_lui_auipc_jal_jalr_addi_add_sub then arithmetic
  else bif inputs.is_compare then .compare
  else bif inputs.instr_xori || inputs.instr_xor then .bitwiseXor
  else bif inputs.instr_ori || inputs.instr_or then .bitwiseOr
  else bif inputs.instr_andi || inputs.instr_and then .bitwiseAnd
  else .zero

def evaluateComparison (comparison : Comparison)
    (reg_op1 reg_op2 : Word) : Bool :=
  match comparison with
  | .equal => equal reg_op1 reg_op2
  | .notEqual => !(equal reg_op1 reg_op2)
  | .signedGreaterOrEqual => !(signedLessThan reg_op1 reg_op2)
  | .unsignedGreaterOrEqual => !(unsignedLessThan reg_op1 reg_op2)
  | .signedLessThan => signedLessThan reg_op1 reg_op2
  | .unsignedLessThan => unsignedLessThan reg_op1 reg_op2

/-- Unsigned ordering on the actual shared arithmetic path. On legal compare
controls the mode is subtraction and this is ordinary unsigned less-than. -/
def sharedUnsignedLess (inputs : Values) : Bool :=
  !(Modules.AddSub.addSubBits 32 inputs.reg_op1 inputs.reg_op2
      (inputs.instr_sub || inputs.is_compare)).2

/-- Signed ordering derived from operand signs and the shared unsigned order. -/
def sharedSignedLess (inputs : Values) : Bool :=
  if inputs.reg_op1 31 = inputs.reg_op2 31 then sharedUnsignedLess inputs
  else inputs.reg_op1 31

/-- The source's one-bit comparison path is independent of whether its
zero-extended value is selected onto `alu_out`. No selector totalizes to false;
overlapping selectors follow the source case order. Inconsistent decoder
controls retain the behavior of the one shared AddSub rather than requiring
extra validity-detection hardware. -/
def comparisonOutput (inputs : Values) : Bool :=
  bif inputs.instr_beq then equal inputs.reg_op1 inputs.reg_op2
  else bif inputs.instr_bne then !(equal inputs.reg_op1 inputs.reg_op2)
  else bif inputs.instr_bge then !(sharedSignedLess inputs)
  else bif inputs.instr_bgeu then !(sharedUnsignedLess inputs)
  else bif inputs.is_slti_blt_slt then sharedSignedLess inputs
  else bif inputs.is_sltiu_bltu_sltu then sharedUnsignedLess inputs
  else false

def evaluateOperation (operation : Operation) (comparison : Bool)
    (reg_op1 reg_op2 : Word) : Word :=
  match operation with
  | .zero => wordOfNat 0
  | .add => addSub false reg_op1 reg_op2
  | .subtract => addSub true reg_op1 reg_op2
  | .compare => wordOfBool comparison
  | .bitwiseXor => bitwiseXor reg_op1 reg_op2
  | .bitwiseOr => bitwiseOr reg_op1 reg_op2
  | .bitwiseAnd => bitwiseAnd reg_op1 reg_op2

@[simp] private theorem evaluateOperation_bif (select : Bool)
    (whenTrue whenFalse : Operation) (comparison : Bool)
    (reg_op1 reg_op2 : Word) :
    evaluateOperation (bif select then whenTrue else whenFalse)
        comparison reg_op1 reg_op2 =
      bif select then evaluateOperation whenTrue comparison reg_op1 reg_op2
      else evaluateOperation whenFalse comparison reg_op1 reg_op2 := by
  cases select <;> rfl

@[simp] private theorem addSub_bif (select : Bool) (reg_op1 reg_op2 : Word) :
    (bif select then addSub true reg_op1 reg_op2
      else addSub false reg_op1 reg_op2) = addSub select reg_op1 reg_op2 := by
  cases select <;> rfl

def evaluate (inputs : Values) : Result :=
  let comparison := comparisonOutput inputs
  {
    alu_out := evaluateOperation (selectedOperation inputs) comparison
      inputs.reg_op1 inputs.reg_op2
    alu_out_0 := comparison
  }

def aluOut (inputs : Values) : Word := (evaluate inputs).alu_out

def aluOut0 (inputs : Values) : Bool := (evaluate inputs).alu_out_0

def valuesOf (inputs : ports.inputs.Values) : Values where
  reg_op1 := inputs .reg_op1
  reg_op2 := inputs .reg_op2
  instr_sub := inputs .instr_sub
  instr_beq := inputs .instr_beq
  instr_bne := inputs .instr_bne
  instr_bge := inputs .instr_bge
  instr_bgeu := inputs .instr_bgeu
  is_slti_blt_slt := inputs .is_slti_blt_slt
  is_sltiu_bltu_sltu := inputs .is_sltiu_bltu_sltu
  is_lui_auipc_jal_jalr_addi_add_sub :=
    inputs .is_lui_auipc_jal_jalr_addi_add_sub
  is_compare := inputs .is_compare
  instr_xori := inputs .instr_xori
  instr_xor := inputs .instr_xor
  instr_ori := inputs .instr_ori
  instr_or := inputs .instr_or
  instr_andi := inputs .instr_andi
  instr_and := inputs .instr_and

def resultValues (result : Result) : ports.outputs.Values
  | .alu_out => result.alu_out
  | .alu_out_0 => result.alu_out_0

def outputRule :
    Contracts.Cycle.CycleOutputRule ports emptySignalMap where
  readsInputs := .all ports.inputs
  writesOutputs := .all ports.outputs
  target inputs _ := resultValues (evaluate (valuesOf inputs))

module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule apply := outputRule
  state_rule where
    reads := []
    next := {}

private def selectedAluOut (inputs : ports.inputs.Values) : Word :=
  bif inputs .is_lui_auipc_jal_jalr_addi_add_sub then
    addSub (inputs .instr_sub || inputs .is_compare)
      (inputs .reg_op1) (inputs .reg_op2)
  else bif inputs .is_compare then wordOfBool (comparisonOutput (valuesOf inputs))
  else bif (inputs .instr_xori || inputs .instr_xor) then
    bitwiseXor (inputs .reg_op1) (inputs .reg_op2)
  else bif (inputs .instr_ori || inputs .instr_or) then
    bitwiseOr (inputs .reg_op1) (inputs .reg_op2)
  else bif (inputs .instr_andi || inputs .instr_and) then
    bitwiseAnd (inputs .reg_op1) (inputs .reg_op2)
  else wordOfNat 0

private theorem aluOut_valuesOf (inputs : ports.inputs.Values) :
    aluOut (valuesOf inputs) = selectedAluOut inputs := by
  simp only [aluOut, evaluate, selectedOperation, valuesOf, evaluateOperation_bif]
  simp only [evaluateOperation, addSub_bif]
  rfl

private theorem wordType_bitwiseXor (left right : Word) :
    (SignalType.vector 32 .bit).bitwiseXor left right = bitwiseXor left right := by
  funext index
  simp only [SignalType.bitwiseXor, bitwiseXor]
  cases left index <;> cases right index <;> rfl

@[simp] theorem outputRule_holds_iff
    (inputs : ports.inputs.Values) (state : emptySignalMap.Values)
    (outputs : ports.outputs.Values) :
    outputRule.Holds inputs state outputs ↔
      outputs .alu_out = aluOut (valuesOf inputs) ∧
      outputs .alu_out_0 = aluOut0 (valuesOf inputs) := by
  simp only [outputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal
    exact ⟨congrFun equal .alu_out, congrFun equal .alu_out_0⟩
  · rintro ⟨aluOutEqual, aluOut0Equal⟩
    funext output
    cases output
    · exact aluOutEqual
    · exact aluOut0Equal

/-! ## Hardware structure -/

private abbrev wordType : SignalType := .vector 32 .bit

private def wordSplitter : Composition.SignalSplitter := .vector 32 .bit
private def wordCombiner : Composition.SignalCombiner := .vector 32 .bit

private inductive Instance
  /-- Exposes the operand sign bits to the signed-comparison logic. -/
  | leftSplit | rightSplit
  /-- The sole arithmetic path, shared by addition, subtraction, and order. -/
  | subtractMode | addSub
  /-- Parallel equality and pointwise logic paths from the source ALU. -/
  | equality | bitwiseXor | bitwiseOr | bitwiseAnd
  /-- Shared totalization constants. -/
  | zeroBit | zeroWord
  /-- Comparison flags derived from equality, signs, and subtraction carry. -/
  | unsignedLess | signDifference | signedLess
  | notEqual | notSignedLess | notUnsignedLess
  /-- Source-order comparison selection, from lowest to highest priority. -/
  | selectUnsignedLess | selectSignedLess | selectUnsignedGreaterEqual
  | selectSignedGreaterEqual | selectNotEqual | selectEqual
  /-- Zero-extends the selected comparison into a word. -/
  | comparisonWord
  /-- Combines paired immediate/register selectors for the bitwise paths. -/
  | xorSelected | orSelected | andSelected
  /-- Source-order result selection, from lowest to highest priority. -/
  | selectAnd | selectOr | selectXor | selectComparison | selectArithmetic
deriving Enumeration

@[reducible] private def instancePorts : InstancePorts :=
  EnumeratedMap.of Instance fun
    | .leftSplit | .rightSplit => wordSplitter.ports
    | .subtractMode | .xorSelected | .orSelected | .andSelected =>
        Primitives.or.ports
    | .addSub => Modules.AddSub.ports 32
    | .equality => Modules.Equality.ports wordType
    | .bitwiseXor => Modules.BitwiseXor.ports wordType
    | .bitwiseOr => Modules.BitwiseOr.ports wordType
    | .bitwiseAnd => Modules.BitwiseAnd.ports wordType
    | .zeroBit => Modules.Constant.ports .bit
    | .zeroWord => Modules.Constant.ports wordType
    | .unsignedLess | .notEqual | .notSignedLess | .notUnsignedLess =>
        Primitives.not.ports
    | .signDifference => Primitives.xor.ports
    | .signedLess | .selectUnsignedLess | .selectSignedLess |
        .selectUnsignedGreaterEqual | .selectSignedGreaterEqual |
        .selectNotEqual | .selectEqual => Modules.Mux.ports .bit
    | .comparisonWord => wordCombiner.ports
    | .selectAnd | .selectOr | .selectXor | .selectComparison |
        .selectArithmetic => Modules.Mux.ports wordType

@[reducible] private def context : EndpointContext where
  ports := ports
  instancePorts := instancePorts

private def wiring : Wiring context.ports context.instancePorts := {
  moduleOutput := fun
    | .alu_out => context.instanceOutput .selectArithmetic .result
    | .alu_out_0 => context.instanceOutput .selectEqual .result
  instanceInput := fun
    | .leftSplit, .value => context.moduleInput .reg_op1
    | .rightSplit, .value => context.moduleInput .reg_op2

    -- The shared AddSub subtracts for SUB and for every live comparison.
    | .subtractMode, .left => context.moduleInput .instr_sub
    | .subtractMode, .right => context.moduleInput .is_compare
    | .addSub, .left => context.moduleInput .reg_op1
    | .addSub, .right => context.moduleInput .reg_op2
    | .addSub, .subtract => context.instanceOutput .subtractMode .output

    | .equality, .left => context.moduleInput .reg_op1
    | .equality, .right => context.moduleInput .reg_op2
    | .bitwiseXor, .left => context.moduleInput .reg_op1
    | .bitwiseXor, .right => context.moduleInput .reg_op2
    | .bitwiseOr, .left => context.moduleInput .reg_op1
    | .bitwiseOr, .right => context.moduleInput .reg_op2
    | .bitwiseAnd, .left => context.moduleInput .reg_op1
    | .bitwiseAnd, .right => context.moduleInput .reg_op2
    | .zeroBit, impossible => nomatch impossible
    | .zeroWord, impossible => nomatch impossible

    -- AddSub carry is no-borrow in comparison mode.
    | .unsignedLess, .input => context.instanceOutput .addSub .carryOut
    | .signDifference, .left =>
        context.instanceOutput .leftSplit (Fin.last 31)
    | .signDifference, .right =>
        context.instanceOutput .rightSplit (Fin.last 31)
    | .signedLess, .select => context.instanceOutput .signDifference .output
    | .signedLess, .whenFalse => context.instanceOutput .unsignedLess .output
    | .signedLess, .whenTrue =>
        context.instanceOutput .leftSplit (Fin.last 31)
    | .notEqual, .input => context.instanceOutput .equality .result
    | .notSignedLess, .input => context.instanceOutput .signedLess .result
    | .notUnsignedLess, .input => context.instanceOutput .unsignedLess .output

    -- Comparison case chain. The first mux starts from false.
    | .selectUnsignedLess, .select =>
        context.moduleInput .is_sltiu_bltu_sltu
    | .selectUnsignedLess, .whenFalse => context.instanceOutput .zeroBit .output
    | .selectUnsignedLess, .whenTrue =>
        context.instanceOutput .unsignedLess .output
    | .selectSignedLess, .select => context.moduleInput .is_slti_blt_slt
    | .selectSignedLess, .whenFalse =>
        context.instanceOutput .selectUnsignedLess .result
    | .selectSignedLess, .whenTrue => context.instanceOutput .signedLess .result
    | .selectUnsignedGreaterEqual, .select => context.moduleInput .instr_bgeu
    | .selectUnsignedGreaterEqual, .whenFalse =>
        context.instanceOutput .selectSignedLess .result
    | .selectUnsignedGreaterEqual, .whenTrue =>
        context.instanceOutput .notUnsignedLess .output
    | .selectSignedGreaterEqual, .select => context.moduleInput .instr_bge
    | .selectSignedGreaterEqual, .whenFalse =>
        context.instanceOutput .selectUnsignedGreaterEqual .result
    | .selectSignedGreaterEqual, .whenTrue =>
        context.instanceOutput .notSignedLess .output
    | .selectNotEqual, .select => context.moduleInput .instr_bne
    | .selectNotEqual, .whenFalse =>
        context.instanceOutput .selectSignedGreaterEqual .result
    | .selectNotEqual, .whenTrue => context.instanceOutput .notEqual .output
    | .selectEqual, .select => context.moduleInput .instr_beq
    | .selectEqual, .whenFalse => context.instanceOutput .selectNotEqual .result
    | .selectEqual, .whenTrue => context.instanceOutput .equality .result

    -- Comparison results occupy bit zero, matching Verilog scalar assignment.
    | .comparisonWord, index => if (show Fin 32 from index) = 0 then
        context.instanceOutput .selectEqual .result
      else context.instanceOutput .zeroBit .output

    | .xorSelected, .left => context.moduleInput .instr_xori
    | .xorSelected, .right => context.moduleInput .instr_xor
    | .orSelected, .left => context.moduleInput .instr_ori
    | .orSelected, .right => context.moduleInput .instr_or
    | .andSelected, .left => context.moduleInput .instr_andi
    | .andSelected, .right => context.moduleInput .instr_and

    -- Result case chain. Arithmetic has the highest source-case priority.
    | .selectAnd, .select => context.instanceOutput .andSelected .output
    | .selectAnd, .whenFalse => context.instanceOutput .zeroWord .output
    | .selectAnd, .whenTrue => context.instanceOutput .bitwiseAnd .result
    | .selectOr, .select => context.instanceOutput .orSelected .output
    | .selectOr, .whenFalse => context.instanceOutput .selectAnd .result
    | .selectOr, .whenTrue => context.instanceOutput .bitwiseOr .result
    | .selectXor, .select => context.instanceOutput .xorSelected .output
    | .selectXor, .whenFalse => context.instanceOutput .selectOr .result
    | .selectXor, .whenTrue => context.instanceOutput .bitwiseXor .result
    | .selectComparison, .select => context.moduleInput .is_compare
    | .selectComparison, .whenFalse => context.instanceOutput .selectXor .result
    | .selectComparison, .whenTrue =>
        context.instanceOutput .comparisonWord .value
    | .selectArithmetic, .select =>
        context.moduleInput .is_lui_auipc_jal_jalr_addi_add_sub
    | .selectArithmetic, .whenFalse =>
        context.instanceOutput .selectComparison .result
    | .selectArithmetic, .whenTrue => context.instanceOutput .addSub .result }

@[reducible] private def body : ModuleBody := ⟨context, wiring⟩

private def zeroBitValue : Bool := false
private def zeroWordValue : Word := wordOfNat 0

@[reducible] private def childContracts :
    Contracts.Cycle.ChildCycleContracts body
  | .leftSplit | .rightSplit => wordSplitter.cycleContract
  | .subtractMode | .xorSelected | .orSelected | .andSelected =>
      Primitives.orCycleContract
  | .addSub => Modules.AddSub.cycleContract 32
  | .equality => Modules.Equality.cycleContract wordType
  | .bitwiseXor => Modules.BitwiseXor.cycleContract wordType
  | .bitwiseOr => Modules.BitwiseOr.cycleContract wordType
  | .bitwiseAnd => Modules.BitwiseAnd.cycleContract wordType
  | .zeroBit => Modules.Constant.cycleContract .bit zeroBitValue
  | .zeroWord => Modules.Constant.cycleContract wordType zeroWordValue
  | .unsignedLess | .notEqual | .notSignedLess | .notUnsignedLess =>
      Primitives.notCycleContract
  | .signDifference => Primitives.xorCycleContract
  | .signedLess | .selectUnsignedLess | .selectSignedLess |
      .selectUnsignedGreaterEqual | .selectSignedGreaterEqual |
      .selectNotEqual | .selectEqual => Modules.Mux.cycleContract .bit
  | .comparisonWord => wordCombiner.cycleContract
  | .selectAnd | .selectOr | .selectXor | .selectComparison |
      .selectArithmetic => Modules.Mux.cycleContract wordType

@[reducible] private def structuralChildren :
    (child : instancePorts.Name) → ModuleStructure (instancePorts.ports child)
  | .leftSplit | .rightSplit => wordSplitter.certified.moduleStructure
  | .subtractMode | .xorSelected | .orSelected | .andSelected =>
      Primitives.orCertified.moduleStructure
  | .addSub => Modules.AddSub.moduleStructure 32
  | .equality => Modules.Equality.moduleStructure wordType
  | .bitwiseXor => Modules.BitwiseXor.moduleStructure wordType
  | .bitwiseOr => Modules.BitwiseOr.moduleStructure wordType
  | .bitwiseAnd => Modules.BitwiseAnd.moduleStructure wordType
  | .zeroBit => Modules.Constant.moduleStructure .bit zeroBitValue
  | .zeroWord => Modules.Constant.moduleStructure wordType zeroWordValue
  | .unsignedLess | .notEqual | .notSignedLess | .notUnsignedLess =>
      Primitives.notCertified.moduleStructure
  | .signDifference => Primitives.xorCertified.moduleStructure
  | .signedLess | .selectUnsignedLess | .selectSignedLess |
      .selectUnsignedGreaterEqual | .selectSignedGreaterEqual |
      .selectNotEqual | .selectEqual => Modules.Mux.moduleStructure .bit
  | .comparisonWord => wordCombiner.certified.moduleStructure
  | .selectAnd | .selectOr | .selectXor | .selectComparison |
      .selectArithmetic => Modules.Mux.moduleStructure wordType

/-- Concrete combinational PicoRV32 ALU hierarchy. -/
def moduleStructure : ModuleStructure ports := .composite body structuralChildren

/-! ## Cycle certification -/

private abbrev occurrence (child : Instance)
    (rule : (childContracts child).RuleName) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence body childContracts := ⟨child, rule⟩

private abbrev leftSplitRule :=
  occurrence .leftSplit Composition.SignalComponentRule.apply
private abbrev rightSplitRule :=
  occurrence .rightSplit Composition.SignalComponentRule.apply
private abbrev subtractModeRule := occurrence .subtractMode Primitives.OrRule.apply
private abbrev addSubRule := occurrence .addSub Modules.AddSub.Rule.apply
private abbrev equalityRule := occurrence .equality Modules.Equality.Rule.apply
private abbrev bitwiseXorRule := occurrence .bitwiseXor Modules.BitwiseXor.Rule.apply
private abbrev bitwiseOrRule := occurrence .bitwiseOr Modules.BitwiseOr.Rule.apply
private abbrev bitwiseAndRule := occurrence .bitwiseAnd Modules.BitwiseAnd.Rule.apply
private abbrev zeroBitRule := occurrence .zeroBit Primitives.ConstantRule.apply
private abbrev zeroWordRule := occurrence .zeroWord Primitives.ConstantRule.apply
private abbrev unsignedLessRule := occurrence .unsignedLess Primitives.NotRule.apply
private abbrev signDifferenceRule := occurrence .signDifference Primitives.XorRule.apply
private abbrev signedLessRule := occurrence .signedLess Modules.Mux.Rule.select
private abbrev notEqualRule := occurrence .notEqual Primitives.NotRule.apply
private abbrev notSignedLessRule := occurrence .notSignedLess Primitives.NotRule.apply
private abbrev notUnsignedLessRule := occurrence .notUnsignedLess Primitives.NotRule.apply
private abbrev selectUnsignedLessRule :=
  occurrence .selectUnsignedLess Modules.Mux.Rule.select
private abbrev selectSignedLessRule :=
  occurrence .selectSignedLess Modules.Mux.Rule.select
private abbrev selectUnsignedGreaterEqualRule :=
  occurrence .selectUnsignedGreaterEqual Modules.Mux.Rule.select
private abbrev selectSignedGreaterEqualRule :=
  occurrence .selectSignedGreaterEqual Modules.Mux.Rule.select
private abbrev selectNotEqualRule :=
  occurrence .selectNotEqual Modules.Mux.Rule.select
private abbrev selectEqualRule := occurrence .selectEqual Modules.Mux.Rule.select
private abbrev comparisonWordRule :=
  occurrence .comparisonWord Composition.SignalComponentRule.apply
private abbrev xorSelectedRule := occurrence .xorSelected Primitives.OrRule.apply
private abbrev orSelectedRule := occurrence .orSelected Primitives.OrRule.apply
private abbrev andSelectedRule := occurrence .andSelected Primitives.OrRule.apply
private abbrev selectAndRule := occurrence .selectAnd Modules.Mux.Rule.select
private abbrev selectOrRule := occurrence .selectOr Modules.Mux.Rule.select
private abbrev selectXorRule := occurrence .selectXor Modules.Mux.Rule.select
private abbrev selectComparisonRule :=
  occurrence .selectComparison Modules.Mux.Rule.select
private abbrev selectArithmeticRule :=
  occurrence .selectArithmetic Modules.Mux.Rule.select

@[simp] private theorem leftSplitRule_writes :
    leftSplitRule.writes = List.finRange 32 := rfl
@[simp] private theorem rightSplitRule_writes :
    rightSplitRule.writes = List.finRange 32 := rfl
@[simp] private theorem subtractModeRule_writes : subtractModeRule.writes = [.output] := rfl
@[simp] private theorem addSubRule_writes : addSubRule.writes = [.result, .carryOut] := rfl
@[simp] private theorem equalityRule_writes : equalityRule.writes = [.result] := rfl
@[simp] private theorem bitwiseXorRule_writes : bitwiseXorRule.writes = [.result] := rfl
@[simp] private theorem bitwiseOrRule_writes : bitwiseOrRule.writes = [.result] := rfl
@[simp] private theorem bitwiseAndRule_writes : bitwiseAndRule.writes = [.result] := rfl
@[simp] private theorem zeroBitRule_writes : zeroBitRule.writes = [.output] := rfl
@[simp] private theorem zeroWordRule_writes : zeroWordRule.writes = [.output] := rfl
@[simp] private theorem unsignedLessRule_writes : unsignedLessRule.writes = [.output] := rfl
@[simp] private theorem signDifferenceRule_writes : signDifferenceRule.writes = [.output] := rfl
@[simp] private theorem signedLessRule_writes : signedLessRule.writes = [.result] := rfl
@[simp] private theorem notEqualRule_writes : notEqualRule.writes = [.output] := rfl
@[simp] private theorem notSignedLessRule_writes : notSignedLessRule.writes = [.output] := rfl
@[simp] private theorem notUnsignedLessRule_writes : notUnsignedLessRule.writes = [.output] := rfl
@[simp] private theorem selectUnsignedLessRule_writes :
    selectUnsignedLessRule.writes = [.result] := rfl
@[simp] private theorem selectSignedLessRule_writes :
    selectSignedLessRule.writes = [.result] := rfl
@[simp] private theorem selectUnsignedGreaterEqualRule_writes :
    selectUnsignedGreaterEqualRule.writes = [.result] := rfl
@[simp] private theorem selectSignedGreaterEqualRule_writes :
    selectSignedGreaterEqualRule.writes = [.result] := rfl
@[simp] private theorem selectNotEqualRule_writes : selectNotEqualRule.writes = [.result] := rfl
@[simp] private theorem selectEqualRule_writes : selectEqualRule.writes = [.result] := rfl
@[simp] private theorem comparisonWordRule_writes : comparisonWordRule.writes = [.value] := rfl
@[simp] private theorem xorSelectedRule_writes : xorSelectedRule.writes = [.output] := rfl
@[simp] private theorem orSelectedRule_writes : orSelectedRule.writes = [.output] := rfl
@[simp] private theorem andSelectedRule_writes : andSelectedRule.writes = [.output] := rfl
@[simp] private theorem selectAndRule_writes : selectAndRule.writes = [.result] := rfl
@[simp] private theorem selectOrRule_writes : selectOrRule.writes = [.result] := rfl
@[simp] private theorem selectXorRule_writes : selectXorRule.writes = [.result] := rfl
@[simp] private theorem selectComparisonRule_writes : selectComparisonRule.writes = [.result] := rfl
@[simp] private theorem selectArithmeticRule_writes : selectArithmeticRule.writes = [.result] := rfl


private def scheduleOrders :
    ScheduleDerivation.RuleScheduleOrders body childContracts cycleContract where
  output := fun | .apply => [leftSplitRule, rightSplitRule, subtractModeRule, addSubRule,
        equalityRule, bitwiseXorRule, bitwiseOrRule, bitwiseAndRule,
        zeroBitRule, zeroWordRule, unsignedLessRule, signDifferenceRule,
        signedLessRule, notEqualRule, notSignedLessRule, notUnsignedLessRule,
        selectUnsignedLessRule, selectSignedLessRule,
        selectUnsignedGreaterEqualRule, selectSignedGreaterEqualRule,
        selectNotEqualRule, selectEqualRule, comparisonWordRule,
        xorSelectedRule, orSelectedRule, andSelectedRule,
        selectAndRule, selectOrRule, selectXorRule,
        selectComparisonRule, selectArithmeticRule]
  state := []

private def derivedRuleSchedules :
    ScheduleDerivation.DerivedRuleSchedules body childContracts cycleContract := by
  derive_rule_schedules scheduleOrders

private abbrev ruleSchedules := derivedRuleSchedules.schedules

private theorem coversChildren : ruleSchedules.CoversChildren :=
  derivedRuleSchedules.coversChildren

section LayerCertification

variable (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
  body childContracts)

private def stateCorresponds (_ : cycleContract.state.Values)
    (_ : (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren).State) : Prop := True

private theorem implements :
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren)
      cycleContract (stateCorresponds layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  derive_empty_state_child_matches childMatch from
    layerChildren, inputs, structuralState, proposal, satisfies
  have leftSplitEquation :=
    (wordSplitter.outputRule_holds_iff _ _ _).mp ((childMatch .leftSplit).1.1 .apply)
  have rightSplitEquation :=
    (wordSplitter.outputRule_holds_iff _ _ _).mp ((childMatch .rightSplit).1.1 .apply)
  have leftSign : (proposal.2 .leftSplit).outputs (Fin.last 31) = inputs .reg_op1 31 := by
    have equation := congrFun leftSplitEquation (Fin.last 31)
    simpa [ProposedValues.childInputs_apply, body, wiring, context, EndpointContext.moduleInput, EndpointContext.instanceOutput,
      Composition.SignalSplitter.outputValues, wordSplitter, SignalSource.value] using equation
  have rightSign : (proposal.2 .rightSplit).outputs (Fin.last 31) = inputs .reg_op2 31 := by
    have equation := congrFun rightSplitEquation (Fin.last 31)
    simpa [ProposedValues.childInputs_apply, body, wiring, context, EndpointContext.moduleInput, EndpointContext.instanceOutput,
      Composition.SignalSplitter.outputValues, wordSplitter, SignalSource.value] using equation
  have subtractModeValue : (proposal.2 .subtractMode).outputs .output =
      (inputs .instr_sub || inputs .is_compare) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .subtractMode).1.1 .apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context, EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] using equation
  have addSubResult : (proposal.2 .addSub).outputs .result =
      (Modules.AddSub.addSubBits 32 (inputs .reg_op1) (inputs .reg_op2)
        (inputs .instr_sub || inputs .is_compare)).1 := by
    have equation := Modules.AddSub.result_of_evaluatesTo 32 _ _ _ _ (childMatch .addSub).1
    simpa [ProposedValues.childInputs_apply, body, wiring, context, EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value,
      subtractModeValue] using equation
  have addSubCarry : (proposal.2 .addSub).outputs .carryOut =
      (Modules.AddSub.addSubBits 32 (inputs .reg_op1) (inputs .reg_op2)
        (inputs .instr_sub || inputs .is_compare)).2 := by
    have equation := Modules.AddSub.carry_of_evaluatesTo 32 _ _ _ _ (childMatch .addSub).1
    simpa [ProposedValues.childInputs_apply, body, wiring, context, EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value,
      subtractModeValue] using equation
  child_contract_fact equalityValue : (proposal.2 .equality).outputs .result =
      wordType.equal (inputs .reg_op1) (inputs .reg_op2) from
      (childMatch .equality).1 using
      Modules.Equality.result_of_evaluatesTo wordType _ _ _ _ unfolding body, wiring, context
  child_contract_fact bitwiseXorValue : (proposal.2 .bitwiseXor).outputs .result =
      wordType.bitwiseXor (inputs .reg_op1) (inputs .reg_op2) from
      (childMatch .bitwiseXor).1 using
      Modules.BitwiseXor.result_of_evaluatesTo wordType _ _ _ _ unfolding body, wiring, context
  child_contract_fact bitwiseOrValue : (proposal.2 .bitwiseOr).outputs .result =
      wordType.bitwiseOr (inputs .reg_op1) (inputs .reg_op2) from
      (childMatch .bitwiseOr).1 using
      Modules.BitwiseOr.result_of_evaluatesTo wordType _ _ _ _ unfolding body, wiring, context
  child_contract_fact bitwiseAndValue : (proposal.2 .bitwiseAnd).outputs .result =
      wordType.bitwiseAnd (inputs .reg_op1) (inputs .reg_op2) from
      (childMatch .bitwiseAnd).1 using
      Modules.BitwiseAnd.result_of_evaluatesTo wordType _ _ _ _ unfolding body, wiring, context
  have zeroBitValueEquation : (proposal.2 .zeroBit).outputs .output = false := by
    have equation := Modules.Constant.output_of_evaluatesTo .bit zeroBitValue _ _ _ _
      (childMatch .zeroBit).1
    simpa [zeroBitValue] using equation
  have zeroWordValueEquation : (proposal.2 .zeroWord).outputs .output = wordOfNat 0 := by
    have equation := Modules.Constant.output_of_evaluatesTo wordType zeroWordValue _ _ _ _
      (childMatch .zeroWord).1
    simpa [zeroWordValue] using equation
  have unsignedLessValue : (proposal.2 .unsignedLess).outputs .output =
      sharedUnsignedLess (valuesOf inputs) := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .unsignedLess).1.1 .apply)
    have normalized : (proposal.2 .unsignedLess).outputs .output =
        !((proposal.2 .addSub).outputs .carryOut) := by
      simpa [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value] using equation
    rw [normalized, addSubCarry]
    rfl
  have signDifferenceValue : (proposal.2 .signDifference).outputs .output =
      Bool.xor (inputs .reg_op1 31) (inputs .reg_op2 31) := by
    have equation := (Primitives.xorOutputRule_holds_iff _ _ _).mp
      ((childMatch .signDifference).1.1 .apply)
    have normalized : (proposal.2 .signDifference).outputs .output =
        Primitives.xorValue ((proposal.2 .leftSplit).outputs (Fin.last 31))
          ((proposal.2 .rightSplit).outputs (Fin.last 31)) := by
      simpa [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value] using equation
    rw [normalized, leftSign, rightSign]
    cases inputs .reg_op1 31 <;> cases inputs .reg_op2 31 <;> rfl
  have signedLessValue : (proposal.2 .signedLess).outputs .result =
      sharedSignedLess (valuesOf inputs) := by
    have equation := Modules.Mux.result_of_evaluatesTo .bit _ _ _ _
      (childMatch .signedLess).1
    simp only [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput,
      SignalSource.value] at equation
    rw [equation, signDifferenceValue, unsignedLessValue, leftSign]
    cases left : inputs .reg_op1 31 <;> cases right : inputs .reg_op2 31 <;>
      simp [sharedSignedLess, valuesOf, left, right]
  have notEqualValue : (proposal.2 .notEqual).outputs .output =
      !(equal (inputs .reg_op1) (inputs .reg_op2)) := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notEqual).1.1 .apply)
    have normalized : (proposal.2 .notEqual).outputs .output =
        !((proposal.2 .equality).outputs .result) := by
      simpa [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value] using equation
    rw [normalized, equalityValue, ← equal_eq_signalEqual]
  have notSignedLessValue : (proposal.2 .notSignedLess).outputs .output =
      !(sharedSignedLess (valuesOf inputs)) := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notSignedLess).1.1 .apply)
    have normalized : (proposal.2 .notSignedLess).outputs .output =
        !((proposal.2 .signedLess).outputs .result) := by
      simpa [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value] using equation
    rw [normalized, signedLessValue]
  have notUnsignedLessValue : (proposal.2 .notUnsignedLess).outputs .output =
      !(sharedUnsignedLess (valuesOf inputs)) := by
    have equation := (Primitives.notOutputRule_holds_iff _ _ _).mp
      ((childMatch .notUnsignedLess).1.1 .apply)
    have normalized : (proposal.2 .notUnsignedLess).outputs .output =
        !((proposal.2 .unsignedLess).outputs .output) := by
      simpa [ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value] using equation
    rw [normalized, unsignedLessValue]
  have selectUnsignedLessValue : (proposal.2 .selectUnsignedLess).outputs .result =
      bif inputs .is_sltiu_bltu_sltu then sharedUnsignedLess (valuesOf inputs) else false := by
    have equation := Modules.Mux.result_of_evaluatesTo .bit _ _ _ _
      (childMatch .selectUnsignedLess).1
    simp only [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] at equation
    rw [equation, zeroBitValueEquation, unsignedLessValue]
    rfl
  have selectSignedLessValue : (proposal.2 .selectSignedLess).outputs .result =
      bif inputs .is_slti_blt_slt then sharedSignedLess (valuesOf inputs)
      else bif inputs .is_sltiu_bltu_sltu then sharedUnsignedLess (valuesOf inputs) else false := by
    have equation := Modules.Mux.result_of_evaluatesTo .bit _ _ _ _
      (childMatch .selectSignedLess).1
    simp only [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] at equation
    rw [equation, selectUnsignedLessValue, signedLessValue]
    rfl
  have selectUnsignedGreaterEqualValue :
      (proposal.2 .selectUnsignedGreaterEqual).outputs .result =
        bif inputs .instr_bgeu then !(sharedUnsignedLess (valuesOf inputs))
        else bif inputs .is_slti_blt_slt then sharedSignedLess (valuesOf inputs)
        else bif inputs .is_sltiu_bltu_sltu then sharedUnsignedLess (valuesOf inputs)
        else false := by
    have equation := Modules.Mux.result_of_evaluatesTo .bit _ _ _ _
      (childMatch .selectUnsignedGreaterEqual).1
    simp only [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] at equation
    rw [equation, selectSignedLessValue, notUnsignedLessValue]
    rfl
  have selectSignedGreaterEqualValue :
      (proposal.2 .selectSignedGreaterEqual).outputs .result =
        bif inputs .instr_bge then !(sharedSignedLess (valuesOf inputs))
        else bif inputs .instr_bgeu then !(sharedUnsignedLess (valuesOf inputs))
        else bif inputs .is_slti_blt_slt then sharedSignedLess (valuesOf inputs)
        else bif inputs .is_sltiu_bltu_sltu then sharedUnsignedLess (valuesOf inputs)
        else false := by
    have equation := Modules.Mux.result_of_evaluatesTo .bit _ _ _ _
      (childMatch .selectSignedGreaterEqual).1
    simp only [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] at equation
    rw [equation, selectUnsignedGreaterEqualValue, notSignedLessValue]
    rfl
  have selectNotEqualValue : (proposal.2 .selectNotEqual).outputs .result =
      bif inputs .instr_bne then !(equal (inputs .reg_op1) (inputs .reg_op2))
      else bif inputs .instr_bge then !(sharedSignedLess (valuesOf inputs))
      else bif inputs .instr_bgeu then !(sharedUnsignedLess (valuesOf inputs))
      else bif inputs .is_slti_blt_slt then sharedSignedLess (valuesOf inputs)
      else bif inputs .is_sltiu_bltu_sltu then sharedUnsignedLess (valuesOf inputs)
      else false := by
    have equation := Modules.Mux.result_of_evaluatesTo .bit _ _ _ _
      (childMatch .selectNotEqual).1
    simp only [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] at equation
    rw [equation, selectSignedGreaterEqualValue, notEqualValue]
    rfl
  have selectEqualValue : (proposal.2 .selectEqual).outputs .result =
      comparisonOutput (valuesOf inputs) := by
    have equation := Modules.Mux.result_of_evaluatesTo .bit _ _ _ _
      (childMatch .selectEqual).1
    simp only [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] at equation
    rw [equation, selectNotEqualValue, equalityValue, ← equal_eq_signalEqual]
    unfold comparisonOutput valuesOf
    rfl
  have comparisonWordValue : (proposal.2 .comparisonWord).outputs .value =
      wordOfBool (comparisonOutput (valuesOf inputs)) := by
    have equation := (wordCombiner.outputRule_holds_iff _ _ _).mp
      ((childMatch .comparisonWord).1.1 .apply)
    have valueEquation := congrFun equation .value
    rw [valueEquation]
    funext index
    change Fin 32 at index
    by_cases first : index = 0
    · subst index
      simp [Composition.SignalCombiner.outputValues, wordCombiner,
        ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, selectEqualValue, wordOfBool]
    · simp [Composition.SignalCombiner.outputValues, wordCombiner,
        ProposedValues.childInputs_apply, body, wiring, context,
        EndpointContext.instanceOutput, SignalSource.value, first,
        wordOfBool]
      exact zeroBitValueEquation
  have xorSelectedValue : (proposal.2 .xorSelected).outputs .output =
      (inputs .instr_xori || inputs .instr_xor) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .xorSelected).1.1 .apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] using equation
  have orSelectedValue : (proposal.2 .orSelected).outputs .output =
      (inputs .instr_ori || inputs .instr_or) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .orSelected).1.1 .apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] using equation
  have andSelectedValue : (proposal.2 .andSelected).outputs .output =
      (inputs .instr_andi || inputs .instr_and) := by
    have equation := (Primitives.orOutputRule_holds_iff _ _ _).mp
      ((childMatch .andSelected).1.1 .apply)
    simpa [ProposedValues.childInputs_apply, body, wiring, context,
      EndpointContext.moduleInput, EndpointContext.instanceOutput, SignalSource.value] using equation
  -- Follow the result-selection mux chain.  Intermediate expressions are
  -- inferred instead of restating the progressively larger nested `bif`.
  have selectAndValue := Modules.Mux.result_of_evaluatesTo wordType _ _ _ _
    (childMatch .selectAnd).1
  normalize_child_hyp selectAndValue unfolding body, wiring, context
  rw [andSelectedValue, zeroWordValueEquation, bitwiseAndValue] at selectAndValue
  have selectOrValue := Modules.Mux.result_of_evaluatesTo wordType _ _ _ _
    (childMatch .selectOr).1
  normalize_child_hyp selectOrValue unfolding body, wiring, context
  rw [orSelectedValue, selectAndValue, bitwiseOrValue] at selectOrValue
  have selectXorValue := Modules.Mux.result_of_evaluatesTo wordType _ _ _ _
    (childMatch .selectXor).1
  normalize_child_hyp selectXorValue unfolding body, wiring, context
  rw [xorSelectedValue, selectOrValue, bitwiseXorValue, wordType_bitwiseXor] at selectXorValue
  have selectComparisonValue := Modules.Mux.result_of_evaluatesTo wordType _ _ _ _
    (childMatch .selectComparison).1
  normalize_child_hyp selectComparisonValue unfolding body, wiring, context
  rw [selectXorValue, comparisonWordValue] at selectComparisonValue
  have selectArithmeticValue := Modules.Mux.result_of_evaluatesTo wordType _ _ _ _
    (childMatch .selectArithmetic).1
  normalize_child_hyp selectArithmeticValue unfolding body, wiring, context
  rw [selectComparisonValue, addSubResult] at selectArithmeticValue
  have aluOutBoundary : proposal.1 .alu_out =
      (proposal.2 .selectArithmetic).outputs .result := by
    simpa [body, wiring, context, EndpointContext.instanceOutput, SignalSource.value] using
      satisfies.1 .alu_out
  have aluOut0Boundary : proposal.1 .alu_out_0 =
      (proposal.2 .selectEqual).outputs .result := by
    simpa [body, wiring, context, EndpointContext.instanceOutput, SignalSource.value] using
      satisfies.1 .alu_out_0
  have addSubBehavior (subtract : Bool) :
      addSub subtract (inputs .reg_op1) (inputs .reg_op2) =
        (Modules.AddSub.addSubBits 32 (inputs .reg_op1) (inputs .reg_op2) subtract).1 := by
    apply BitVector.toNat_injective 32
    rw [Modules.AddSub.addSubBits_result_toNat]
    cases subtract <;>
      simp [addSub, wordOfNat, BitVector.toNat_ofNat]
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    constructor
    · change proposal.1 .alu_out = aluOut (valuesOf inputs)
      rw [aluOutBoundary, selectArithmeticValue, aluOut_valuesOf]
      rw [← addSubBehavior (inputs .instr_sub || inputs .is_compare)]
      rfl
    · change proposal.1 .alu_out_0 = aluOut0 (valuesOf inputs)
      rw [aluOut0Boundary, selectEqualValue]
      rfl
  · rfl

private theorem hasCorrespondingState
    (structuralState :
      (Contracts.Cycle.Certification.Layer.moduleStructure body layerChildren).State) :
    ∃ contractState, stateCorresponds layerChildren contractState structuralState :=
  ⟨SignalMap.emptyValues, trivial⟩

end LayerCertification

noncomputable opaque certifiedLayer :
    Contracts.Cycle.ModuleCycleCertifiedLayer body childContracts cycleContract :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    ruleSchedules coversChildren stateCorresponds hasCorrespondingState implements

@[reducible] private noncomputable def certifiedChildren :
    Contracts.Cycle.Certification.Layer.ChildStructures body childContracts
  | .leftSplit | .rightSplit => wordSplitter.certified.certifiedStructure
  | .subtractMode | .xorSelected | .orSelected | .andSelected =>
      Primitives.orCertified.certifiedStructure
  | .addSub => (Modules.AddSub.certified 32).certifiedStructure
  | .equality => (Modules.Equality.certified wordType).certifiedStructure
  | .bitwiseXor => (Modules.BitwiseXor.certified wordType).certifiedStructure
  | .bitwiseOr => (Modules.BitwiseOr.certified wordType).certifiedStructure
  | .bitwiseAnd => (Modules.BitwiseAnd.certified wordType).certifiedStructure
  | .zeroBit => (Modules.Constant.certified .bit zeroBitValue).certifiedStructure
  | .zeroWord => (Modules.Constant.certified wordType zeroWordValue).certifiedStructure
  | .unsignedLess | .notEqual | .notSignedLess | .notUnsignedLess =>
      Primitives.notCertified.certifiedStructure
  | .signDifference => Primitives.xorCertified.certifiedStructure
  | .signedLess | .selectUnsignedLess | .selectSignedLess |
      .selectUnsignedGreaterEqual | .selectSignedGreaterEqual |
      .selectNotEqual | .selectEqual => (Modules.Mux.certified .bit).certifiedStructure
  | .comparisonWord => wordCombiner.certified.certifiedStructure
  | .selectAnd | .selectOr | .selectXor | .selectComparison |
      .selectArithmetic => (Modules.Mux.certified wordType).certifiedStructure

noncomputable opaque certification :
    Contracts.Cycle.ModuleCycleCertification moduleStructure cycleContract :=
  certifiedLayer.certifyComposite structuralChildren certifiedChildren (by
    intro child
    cases child <;> rfl)

/-- The concrete combinational PicoRV32 ALU hierarchy certified against its
cycle contract. -/
noncomputable def certified : Contracts.Cycle.ModuleCycleCertified ports :=
  certification.bundle

@[simp] theorem certified_moduleStructure :
    certified.moduleStructure = moduleStructure := rfl

@[simp] theorem certified_cycleContract :
    certified.cycleContract = cycleContract := rfl

/-- The ALU hierarchy and every reusable child below it have concrete structure. -/
theorem hasExactlyOneSolution (inputs : ports.inputs.Values)
    (currentState : moduleStructure.State) :
    ∃ proposal, moduleStructure.IsSolution inputs currentState proposal ∧
      ∀ other, moduleStructure.IsSolution inputs currentState other → other = proposal :=
  certified.hasExactlyOneStructuralResult inputs currentState

end Silean.Examples.PicoRV.Alu

namespace Silean.Examples.PicoRV.Alu.Naming

open Silean Silean.Naming

def naming : ModuleNaming Alu.moduleStructure := by
  unfold Alu.moduleStructure
  exact .composite ⟨"picorv32_alu", "structural", []⟩ ports
    (fun
      | .leftSplit => "reg_op1_bits"
      | .rightSplit => "reg_op2_bits"
      | .subtractMode => "subtract_mode"
      | .addSub => "add_sub"
      | .equality => "equality"
      | .bitwiseXor => "bitwise_xor"
      | .bitwiseOr => "bitwise_or"
      | .bitwiseAnd => "bitwise_and"
      | .zeroBit => "zero_bit"
      | .zeroWord => "zero_word"
      | .unsignedLess => "unsigned_less"
      | .signDifference => "sign_difference"
      | .signedLess => "signed_less"
      | .notEqual => "not_equal"
      | .notSignedLess => "not_signed_less"
      | .notUnsignedLess => "not_unsigned_less"
      | .selectUnsignedLess => "select_unsigned_less"
      | .selectSignedLess => "select_signed_less"
      | .selectUnsignedGreaterEqual => "select_unsigned_greater_equal"
      | .selectSignedGreaterEqual => "select_signed_greater_equal"
      | .selectNotEqual => "select_not_equal"
      | .selectEqual => "select_equal"
      | .comparisonWord => "comparison_word"
      | .xorSelected => "xor_selected"
      | .orSelected => "or_selected"
      | .andSelected => "and_selected"
      | .selectAnd => "select_and"
      | .selectOr => "select_or"
      | .selectXor => "select_xor"
      | .selectComparison => "select_comparison"
      | .selectArithmetic => "select_arithmetic")
    (fun
      | .leftSplit | .rightSplit => SignalAdapter.splitter Alu.wordSplitter
      | .subtractMode | .xorSelected | .orSelected | .andSelected => Primitive.or
      | .addSub => Modules.AddSub.naming 32
      | .equality => Modules.Equality.Naming.namingWith Alu.wordType
          (.positional Alu.wordType)
      | .bitwiseXor => Modules.BitwiseXor.Naming.namingWith Alu.wordType
          (.positional Alu.wordType)
      | .bitwiseOr => Modules.BitwiseOr.Naming.namingWith Alu.wordType
          (.positional Alu.wordType)
      | .bitwiseAnd => Modules.BitwiseAnd.Naming.namingWith Alu.wordType
          (.positional Alu.wordType)
      | .zeroBit => Modules.Constant.Naming.naming .bit Alu.zeroBitValue
      | .zeroWord => Modules.Constant.Naming.namingWith Alu.wordType
          Alu.zeroWordValue (.positional Alu.wordType)
      | .unsignedLess | .notEqual | .notSignedLess | .notUnsignedLess => Primitive.not
      | .signDifference => Primitive.xor
      | .signedLess | .selectUnsignedLess | .selectSignedLess |
          .selectUnsignedGreaterEqual | .selectSignedGreaterEqual | .selectNotEqual |
          .selectEqual => Modules.Mux.naming .bit
      | .comparisonWord => SignalAdapter.combiner Alu.wordCombiner
      | .selectAnd | .selectOr | .selectXor | .selectComparison | .selectArithmetic =>
          Modules.Mux.namingWith Alu.wordType (.positional Alu.wordType))

def namedModule : NamedModule where
  ports := Alu.ports
  moduleStructure := Alu.moduleStructure
  naming := naming

end Silean.Examples.PicoRV.Alu.Naming
