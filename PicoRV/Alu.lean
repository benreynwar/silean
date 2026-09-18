import Silean.Foundation.BitVector
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModuleDesign
import Silean.Contracts.Cycle.CycleContract
import Silean.Contracts.Cycle.CycleEvaluation
import Silean.Modules.AddSub.AddSub
import Silean.Modules.BitwiseAnd.BitwiseAnd
import Silean.Modules.BitwiseOr.BitwiseOr
import Silean.Modules.BitwiseXor.BitwiseXor
import Silean.Modules.Constant.Constant
import Silean.Modules.Equality.Equality
import Silean.Modules.Mux.Mux
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming
import Silean.Primitives.Not
import Silean.Primitives.Or
import Silean.Primitives.Xor

namespace PicoRV.Alu

open Silean
open Silean.Authoring

/-! Natural behavior, cycle contract, and concrete structure for the
combinational PicoRV32 ALU. The boundary names and operation-selection
behavior follow the selected source configuration. -/

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

def wordOfNat (value : Nat) : Word := Silean.BitVector.ofNat 32 value

def wordOfBool (value : Bool) : Word := fun index =>
  if index = 0 then value else false

def addSub (instr_sub : Bool) (reg_op1 reg_op2 : Word) : Word :=
  let modulus := Silean.BitVector.cardinality 32
  let left := Silean.BitVector.toNat 32 reg_op1
  let right := Silean.BitVector.toNat 32 reg_op2
  if instr_sub then wordOfNat ((left + modulus - right) % modulus)
  else wordOfNat ((left + right) % modulus)

def equal (reg_op1 reg_op2 : Word) : Bool :=
  decide (Silean.BitVector.toNat 32 reg_op1 = Silean.BitVector.toNat 32 reg_op2)

def unsignedLessThan (reg_op1 reg_op2 : Word) : Bool :=
  decide (Silean.BitVector.toNat 32 reg_op1 < Silean.BitVector.toNat 32 reg_op2)

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
  !(Silean.Modules.AddSub.addSubBits 32 inputs.reg_op1 inputs.reg_op2
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
    Silean.Contracts.Cycle.CycleOutputRule ports emptySignalMap where
  readsInputs := .all ports.inputs
  writesOutputs := .all ports.outputs
  target inputs _ := resultValues (evaluate (valuesOf inputs))

module_cycle_contract cycleContract for ports where
  state := emptySignalMap
  output_rule apply := outputRule
  state_rule where
    reads := []
    next := {}

@[simp] theorem outputRule_holds_iff
    (inputs : ports.inputs.Values) (state : emptySignalMap.Values)
    (outputs : ports.outputs.Values) :
    outputRule.Holds inputs state outputs ↔
      outputs .alu_out = aluOut (valuesOf inputs) ∧
      outputs .alu_out_0 = aluOut0 (valuesOf inputs) := by
  simp only [outputRule, Silean.Contracts.Cycle.CycleOutputRule.Holds,
    Silean.SignalGroup.all_matches]
  constructor
  · intro equal
    exact ⟨congrFun equal .alu_out, congrFun equal .alu_out_0⟩
  · rintro ⟨aluOutEqual, aluOut0Equal⟩
    funext output
    cases output
    · exact aluOutEqual
    · exact aluOut0Equal

/-! ## Hardware structure -/

abbrev wordType : SignalType := .vector 32 .bit

def wordSplitter : Silean.Composition.SignalSplitter := .vector 32 .bit
def wordCombiner : Silean.Composition.SignalCombiner := .vector 32 .bit

def zeroBitValue : Bool := false
def zeroWordValue : Word := wordOfNat 0

end PicoRV.Alu

namespace PicoRV

open Silean
open Silean.Authoring

module_design Alu (name := "picorv32_alu") where
  boundary (Alu.ports) (naming := Alu.Naming.ports)
  instances {
    -- Expose operand sign bits and share one arithmetic path.
    leftSplit := Naming.SignalAdapter.splitterDesign Alu.wordSplitter,
    rightSplit := Naming.SignalAdapter.splitterDesign Alu.wordSplitter,
    subtractMode := Silean.Primitives.orDesign,
    addSub := Silean.Modules.AddSub.design 32,
    -- Compute equality and bitwise candidates in parallel.
    equality := Silean.Modules.Equality.design Alu.wordType,
    bitwiseXor := Silean.Modules.BitwiseXor.design Alu.wordType,
    bitwiseOr := Silean.Modules.BitwiseOr.design Alu.wordType,
    bitwiseAnd := Silean.Modules.BitwiseAnd.design Alu.wordType,
    zeroBit := Silean.Modules.Constant.design .bit Alu.zeroBitValue,
    zeroWord := Silean.Modules.Constant.design Alu.wordType Alu.zeroWordValue,
    -- Derive comparison flags from equality, signs, and subtraction carry.
    unsignedLess := Silean.Primitives.notDesign,
    signDifference := Silean.Primitives.xorDesign,
    signedLess := Silean.Modules.Mux.design .bit,
    notEqual := Silean.Primitives.notDesign,
    notSignedLess := Silean.Primitives.notDesign,
    notUnsignedLess := Silean.Primitives.notDesign,
    -- Select comparison results in source priority order.
    selectUnsignedLess := Silean.Modules.Mux.design .bit,
    selectSignedLess := Silean.Modules.Mux.design .bit,
    selectUnsignedGreaterEqual := Silean.Modules.Mux.design .bit,
    selectSignedGreaterEqual := Silean.Modules.Mux.design .bit,
    selectNotEqual := Silean.Modules.Mux.design .bit,
    selectEqual := Silean.Modules.Mux.design .bit,
    comparisonWord := Naming.SignalAdapter.combinerDesign Alu.wordCombiner,
    -- Combine instruction selectors and select the final word result.
    xorSelected := Silean.Primitives.orDesign,
    orSelected := Silean.Primitives.orDesign,
    andSelected := Silean.Primitives.orDesign,
    selectAnd := Silean.Modules.Mux.design Alu.wordType,
    selectOr := Silean.Modules.Mux.design Alu.wordType,
    selectXor := Silean.Modules.Mux.design Alu.wordType,
    selectComparison := Silean.Modules.Mux.design Alu.wordType,
    selectArithmetic := Silean.Modules.Mux.design Alu.wordType }
  wiring {
    outputs {
      .alu_out := selectArithmetic.result,
      .alu_out_0 := selectEqual.result }
    instance (.leftSplit) { .value := input.reg_op1 }
    instance (.rightSplit) { .value := input.reg_op2 }
    instance (.subtractMode) {
      .left := input.instr_sub,
      .right := input.is_compare }
    instance (.addSub) {
      .left := input.reg_op1,
      .right := input.reg_op2,
      .subtract := subtractMode.output }
    instance (.equality) {
      .left := input.reg_op1,
      .right := input.reg_op2 }
    instance (.bitwiseXor) {
      .left := input.reg_op1,
      .right := input.reg_op2 }
    instance (.bitwiseOr) {
      .left := input.reg_op1,
      .right := input.reg_op2 }
    instance (.bitwiseAnd) {
      .left := input.reg_op1,
      .right := input.reg_op2 }
    instance (.zeroBit) {}
    instance (.zeroWord) {}
    instance (.unsignedLess) { .input := addSub.carryOut }
    instance (.signDifference) {
      .left := leftSplit[Fin.last 31],
      .right := rightSplit[Fin.last 31] }
    instance (.signedLess) {
      .select := signDifference.output,
      .whenFalse := unsignedLess.output,
      .whenTrue := leftSplit[Fin.last 31] }
    instance (.notEqual) { .input := equality.result }
    instance (.notSignedLess) { .input := signedLess.result }
    instance (.notUnsignedLess) { .input := unsignedLess.output }
    instance (.selectUnsignedLess) {
      .select := input.is_sltiu_bltu_sltu,
      .whenFalse := zeroBit.output,
      .whenTrue := unsignedLess.output }
    instance (.selectSignedLess) {
      .select := input.is_slti_blt_slt,
      .whenFalse := selectUnsignedLess.result,
      .whenTrue := signedLess.result }
    instance (.selectUnsignedGreaterEqual) {
      .select := input.instr_bgeu,
      .whenFalse := selectSignedLess.result,
      .whenTrue := notUnsignedLess.output }
    instance (.selectSignedGreaterEqual) {
      .select := input.instr_bge,
      .whenFalse := selectUnsignedGreaterEqual.result,
      .whenTrue := notSignedLess.output }
    instance (.selectNotEqual) {
      .select := input.instr_bne,
      .whenFalse := selectSignedGreaterEqual.result,
      .whenTrue := notEqual.output }
    instance (.selectEqual) {
      .select := input.instr_beq,
      .whenFalse := selectNotEqual.result,
      .whenTrue := equality.result }
    instance (.comparisonWord) {
      index := from (if (show Fin 32 from index) = 0 then
        c.instanceOutput .selectEqual .result
      else c.instanceOutput .zeroBit .output) }
    instance (.xorSelected) {
      .left := input.instr_xori,
      .right := input.instr_xor }
    instance (.orSelected) {
      .left := input.instr_ori,
      .right := input.instr_or }
    instance (.andSelected) {
      .left := input.instr_andi,
      .right := input.instr_and }
    instance (.selectAnd) {
      .select := andSelected.output,
      .whenFalse := zeroWord.output,
      .whenTrue := bitwiseAnd.result }
    instance (.selectOr) {
      .select := orSelected.output,
      .whenFalse := selectAnd.result,
      .whenTrue := bitwiseOr.result }
    instance (.selectXor) {
      .select := xorSelected.output,
      .whenFalse := selectOr.result,
      .whenTrue := bitwiseXor.result }
    instance (.selectComparison) {
      .select := input.is_compare,
      .whenFalse := selectXor.result,
      .whenTrue := comparisonWord.value }
    instance (.selectArithmetic) {
      .select := input.is_lui_auipc_jal_jalr_addi_add_sub,
      .whenFalse := selectComparison.result,
      .whenTrue := addSub.result }
  }

end PicoRV
