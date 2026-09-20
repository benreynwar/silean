import Silean.Foundation.BitVector
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.CircuitDescription
import Silean.Contracts.Cycle.CycleContract
import Silean.Contracts.Cycle.CycleEvaluation
import PicoRV.Authoring.CircuitLogic
import PicoRV.Internal.AluStructure

namespace PicoRV.Alu

open Silean
open Silean.Authoring

/-! Natural behavior, cycle contract, and concrete structure for the
combinational PicoRV32 ALU. The boundary names and operation-selection
behavior follow the selected source configuration. -/


/-! ## Authored hardware -/

namespace Description

open Silean.Authoring.CircuitDescription
open PicoRV.Authoring
open scoped Silean.Authoring

noncomputable def construction : Builder Unit := do
  let regOp1 ← input "reg_op1" wordType
  let regOp2 ← input "reg_op2" wordType
  let instrSub ← input "instr_sub" .bit
  let instrBeq ← input "instr_beq" .bit
  let instrBne ← input "instr_bne" .bit
  let instrBge ← input "instr_bge" .bit
  let instrBgeu ← input "instr_bgeu" .bit
  let isSltiBltSlt ← input "is_slti_blt_slt" .bit
  let isSltiuBltuSltu ← input "is_sltiu_bltu_sltu" .bit
  let arithmeticSelected ← input "is_lui_auipc_jal_jalr_addi_add_sub" .bit
  let isCompare ← input "is_compare" .bit
  let instrXori ← input "instr_xori" .bit
  let instrXor ← input "instr_xor" .bit
  let instrOri ← input "instr_ori" .bit
  let instrOr ← input "instr_or" .bit
  let instrAndi ← input "instr_andi" .bit
  let instrAnd ← input "instr_and" .bit

  let leftBits ← splitVector 32 .bit regOp1
  let rightBits ← splitVector 32 .bit regOp2
  let subtractMode ← instrSub ||| isCompare
  let arithmetic ← Silean.Modules.AddSub.place regOp1 regOp2 subtractMode
  let equal ← regOp1 === regOp2
  let xorValue ← regOp1 ^^^ regOp2
  let orValue ← regOp1 ||| regOp2
  let andValue ← regOp1 &&& regOp2
  let zeroBit ← constant .bit zeroBitValue
  let zeroWord ← constant wordType zeroWordValue
  let unsignedLess ← !! arithmetic.carryOut
  let signDifference ← leftBits (Fin.last 31) ^^^ rightBits (Fin.last 31)
  let signedLess ← mux signDifference unsignedLess (leftBits (Fin.last 31))
  let notEqual ← !! equal
  let notSignedLess ← !! signedLess
  let notUnsignedLess ← !! unsignedLess

  let comparison ← mux instrBeq
    (← mux instrBne
      (← mux instrBge
        (← mux instrBgeu
          (← mux isSltiBltSlt
            (← mux isSltiuBltuSltu zeroBit unsignedLess)
            signedLess)
          notUnsignedLess)
        notSignedLess)
      notEqual)
    equal
  let comparisonWord ← Silean.Authoring.combine wordCombiner
    fun index => if (show Fin 32 from index) = 0 then comparison else zeroBit
  let xorSelected ← instrXori ||| instrXor
  let orSelected ← instrOri ||| instrOr
  let andSelected ← instrAndi ||| instrAnd
  let selected ← mux arithmeticSelected
    (← mux isCompare
      (← mux xorSelected
        (← mux orSelected
          (← mux andSelected zeroWord andValue)
          orValue)
        xorValue)
      comparisonWord)
    arithmetic.result

  output "alu_out" selected
  output "alu_out_0" comparison

noncomputable def description : Description := build construction

end Description

/-! ## Placement -/

abbrev InputNets :=
  (input : ports.inputs.Label) →
    Authoring.CircuitDescription.Net (ports.inputs.signalType input)

structure PlacedOutputs where
  aluOut : Authoring.CircuitDescription.Net wordType
  aluOut0 : Authoring.CircuitDescription.Net .bit

/-- Place an ALU using the next conventional indexed name. -/
noncomputable def place (inputs : InputNets) :
    Authoring.CircuitDescription.Builder PlacedOutputs := do
  let child ← Authoring.CircuitDescription.placeIndexed "alu" design inputs
  pure { aluOut := child .alu_out, aluOut0 := child .alu_out_0 }

/-- Place an ALU under an explicitly chosen structural name. -/
noncomputable def placeNamed (name : Naming.SourceName) (inputs : InputNets) :
    Authoring.CircuitDescription.Builder PlacedOutputs := do
  let child ← Authoring.CircuitDescription.placeNamed name design inputs
  pure { aluOut := child .alu_out, aluOut0 := child .alu_out_0 }

attribute [circuit_description] place placeNamed

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

end PicoRV.Alu
