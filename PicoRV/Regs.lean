import Silean.Foundation.BitVector
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModuleDesign
import Silean.Contracts.Cycle.CycleEvaluation
import Silean.Modules.Constant.Constant
import Silean.Modules.Equality.Equality
import Silean.Modules.Mux.Mux
import Silean.Modules.RegisterBank.RegisterBank
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.And
import Silean.Primitives.Not

namespace PicoRV.Regs

open Silean
open Silean.Authoring

/-! PicoRV32's 32-entry integer register file. Register zero always reads as
zero and ignores writes. The exact cycle contract is followed by a structural
implementation around the generic two-read `RegisterBank`. -/

abbrev Word := Fin 32 → Bool
abbrev RegisterAddress := Fin 5 → Bool
abbrev RegisterValues := Fin 32 → Word

module_ports ports where
  input resetn : .bit,
  input decoded_rs1 : .vector 5 .bit,
  input decoded_rs2 : .vector 5 .bit,
  input cpuregs_write : .bit,
  input latched_rd : .vector 5 .bit,
  input cpuregs_wrdata : .vector 32 .bit,
  output cpuregs_rs1 : .vector 32 .bit,
  output cpuregs_rs2 : .vector 32 .bit

inductive State
  /-- The 32 architectural integer registers. -/
  | cpuregs
deriving Enumeration

@[reducible] def stateMap : SignalMap :=
  Silean.EnumeratedMap.of State fun
    | .cpuregs => .vector 32 (.vector 32 .bit)

def zeroWord : Word := fun _ => false

def registerIndex (address : RegisterAddress) : Fin 32 :=
  Silean.BitVector.toIndex 5 address

@[simp] theorem registerIndex_eq_zero_iff (address : RegisterAddress) :
    registerIndex address = 0 ↔ address = fun _ => false := by
  constructor
  · intro equal
    apply Silean.BitVector.toNat_injective 5
    have valuesEqual := congrArg Fin.val equal
    simpa [registerIndex, Silean.BitVector.toIndex_val] using valuesEqual
  · rintro rfl
    apply Fin.ext
    simp [registerIndex, Silean.BitVector.toIndex_val]

def readRegister (address : RegisterAddress) (registers : RegisterValues) : Word :=
  if registerIndex address = 0 then zeroWord else registers (registerIndex address)

def nextRegisters (resetn cpuregs_write : Bool)
    (latched_rd : RegisterAddress) (cpuregs_wrdata : Word)
    (registers : RegisterValues) : RegisterValues :=
  fun index =>
    if resetn && cpuregs_write && decide (registerIndex latched_rd ≠ 0) &&
        decide (index = registerIndex latched_rd)
    then cpuregs_wrdata
    else registers index

namespace Rs1Rule
inductive Input | decoded_rs1 deriving Enumeration
inductive Output | cpuregs_rs1 deriving Enumeration
end Rs1Rule

namespace Rs2Rule
inductive Input | decoded_rs2 deriving Enumeration
inductive Output | cpuregs_rs2 deriving Enumeration
end Rs2Rule

namespace UpdateRule
inductive Input | resetn | cpuregs_write | latched_rd | cpuregs_wrdata
deriving Enumeration
end UpdateRule

@[reducible] private def rs1Inputs : SignalGroup inputMap :=
  Silean.SignalGroup.fromLabels inputMap Rs1Rule.Input fun
    | .decoded_rs1 => .decoded_rs1

@[reducible] private def rs1Outputs : SignalGroup outputMap :=
  Silean.SignalGroup.fromLabels outputMap Rs1Rule.Output fun
    | .cpuregs_rs1 => .cpuregs_rs1

@[reducible] private def rs2Inputs : SignalGroup inputMap :=
  Silean.SignalGroup.fromLabels inputMap Rs2Rule.Input fun
    | .decoded_rs2 => .decoded_rs2

@[reducible] private def rs2Outputs : SignalGroup outputMap :=
  Silean.SignalGroup.fromLabels outputMap Rs2Rule.Output fun
    | .cpuregs_rs2 => .cpuregs_rs2

@[reducible] private def updateInputs : SignalGroup inputMap :=
  Silean.SignalGroup.fromLabels inputMap UpdateRule.Input fun
    | .resetn => .resetn
    | .cpuregs_write => .cpuregs_write
    | .latched_rd => .latched_rd
    | .cpuregs_wrdata => .cpuregs_wrdata

def cpuregsRs1Rule :
    Silean.Contracts.Cycle.CycleOutputRule ports stateMap where
  readsInputs := rs1Inputs
  writesOutputs := rs1Outputs
  target inputs state := fun
    | .cpuregs_rs1 => readRegister (inputs .decoded_rs1) (state .cpuregs)

def cpuregsRs2Rule :
    Silean.Contracts.Cycle.CycleOutputRule ports stateMap where
  readsInputs := rs2Inputs
  writesOutputs := rs2Outputs
  target inputs state := fun
    | .cpuregs_rs2 => readRegister (inputs .decoded_rs2) (state .cpuregs)

def stateRule : Silean.Contracts.Cycle.CycleStateRule ports stateMap where
  readsInputs := updateInputs
  target inputs state := fun
    | .cpuregs => nextRegisters (inputs .resetn) (inputs .cpuregs_write)
        (inputs .latched_rd) (inputs .cpuregs_wrdata) (state .cpuregs)

module_cycle_contract cycleContract for ports where
  state := stateMap
  output_rule cpuregs_rs1 := cpuregsRs1Rule
  output_rule cpuregs_rs2 := cpuregsRs2Rule
  state_rule := stateRule

@[simp] theorem readRegister_zero (registers : RegisterValues) :
    readRegister (fun _ => false) registers = zeroWord := by
  have zeroIndex : registerIndex (fun _ => false) = 0 := by
    apply Fin.ext
    simp [registerIndex, Silean.BitVector.toIndex_val]
  simp [readRegister, zeroIndex]

theorem readRegister_nonzero (address : RegisterAddress)
    (registers : RegisterValues) (nonzero : registerIndex address ≠ 0) :
    readRegister address registers = registers (registerIndex address) := by
  simp [readRegister, nonzero]

@[simp] theorem nextRegisters_reset (cpuregs_write : Bool)
    (latched_rd : RegisterAddress) (cpuregs_wrdata : Word)
    (registers : RegisterValues) :
    nextRegisters false cpuregs_write latched_rd cpuregs_wrdata registers = registers := by
  funext index
  simp [nextRegisters]

@[simp] theorem nextRegisters_write_disabled (resetn : Bool)
    (latched_rd : RegisterAddress) (cpuregs_wrdata : Word)
    (registers : RegisterValues) :
    nextRegisters resetn false latched_rd cpuregs_wrdata registers = registers := by
  funext index
  simp [nextRegisters]

theorem nextRegisters_zero (resetn cpuregs_write : Bool)
    (latched_rd : RegisterAddress) (cpuregs_wrdata : Word)
    (registers : RegisterValues) (zero : registerIndex latched_rd = 0) :
    nextRegisters resetn cpuregs_write latched_rd cpuregs_wrdata registers = registers := by
  funext index
  simp [nextRegisters, zero]

@[simp] theorem nextRegisters_written (latched_rd : RegisterAddress)
    (cpuregs_wrdata : Word) (registers : RegisterValues)
    (nonzero : registerIndex latched_rd ≠ 0) :
    nextRegisters true true latched_rd cpuregs_wrdata registers
      (registerIndex latched_rd) = cpuregs_wrdata := by
  simp [nextRegisters, nonzero]

theorem nextRegisters_other (resetn cpuregs_write : Bool)
    (latched_rd : RegisterAddress) (cpuregs_wrdata : Word)
    (registers : RegisterValues) (index : Fin 32)
    (different : index ≠ registerIndex latched_rd) :
    nextRegisters resetn cpuregs_write latched_rd cpuregs_wrdata registers index =
      registers index := by
  simp [nextRegisters, different]

@[simp] theorem cpuregsRs1Rule_holds_iff
    (inputs : ports.inputs.Values) (state : stateMap.Values)
    (outputs : ports.outputs.Values) :
    cpuregsRs1Rule.Holds inputs state outputs ↔
      outputs .cpuregs_rs1 = readRegister (inputs .decoded_rs1) (state .cpuregs) := by
  unfold cpuregsRs1Rule Silean.Contracts.Cycle.CycleOutputRule.Holds
    Silean.SignalGroup.Matches
  constructor
  · intro equal
    exact congrFun equal .cpuregs_rs1
  · intro equal
    funext output
    cases output
    exact equal

@[simp] theorem cpuregsRs2Rule_holds_iff
    (inputs : ports.inputs.Values) (state : stateMap.Values)
    (outputs : ports.outputs.Values) :
    cpuregsRs2Rule.Holds inputs state outputs ↔
      outputs .cpuregs_rs2 = readRegister (inputs .decoded_rs2) (state .cpuregs) := by
  unfold cpuregsRs2Rule Silean.Contracts.Cycle.CycleOutputRule.Holds
    Silean.SignalGroup.Matches
  constructor
  · intro equal
    exact congrFun equal .cpuregs_rs2
  · intro equal
    funext output
    cases output
    exact equal

/-! ## Hardware structure -/

abbrev wordType : SignalType := .vector 32 .bit
abbrev addressType : SignalType := .vector 5 .bit
def zeroAddressValue : addressType.Denote := fun _ => false
def zeroWordValue : wordType.Denote := fun _ => false

end PicoRV.Regs

namespace PicoRV

open Silean
open Silean.Authoring

module_design Regs (name := "picorv32_regs") where
  boundary (Regs.ports) (naming := Regs.Naming.ports)
  instances {
    -- The shared 32-entry storage with two independent read ports.
    bank := Silean.Modules.RegisterBank.design Regs.wordType 5 2,
    -- Shared constants used to protect architectural register zero.
    zeroAddress := Silean.Modules.Constant.design Regs.addressType Regs.zeroAddressValue,
    zeroWord := Silean.Modules.Constant.design Regs.wordType Regs.zeroWordValue,
    -- Test all externally supplied register addresses against zero.
    rs1Zero := Silean.Modules.Equality.design Regs.addressType,
    rs2Zero := Silean.Modules.Equality.design Regs.addressType,
    rdZero := Silean.Modules.Equality.design Regs.addressType,
    -- Form resetn && cpuregs_write && (latched_rd != 0).
    rdNonzero := Silean.Primitives.notDesign,
    requestedWrite := Silean.Primitives.andDesign,
    enabledWrite := Silean.Primitives.andDesign,
    -- Select zero or the stored value for each architectural read.
    rs1Mux := Silean.Modules.Mux.design Regs.wordType,
    rs2Mux := Silean.Modules.Mux.design Regs.wordType }
  wiring {
    outputs {
      .cpuregs_rs1 := rs1Mux.result,
      .cpuregs_rs2 := rs2Mux.result }
    instance (.bank) {
      .readAddress 0 := input.decoded_rs1,
      .readAddress 1 := input.decoded_rs2,
      .writeEnable := enabledWrite.output,
      .writeAddress := input.latched_rd,
      .writeValue := input.cpuregs_wrdata }
    instance (.zeroAddress) {}
    instance (.zeroWord) {}
    instance (.rs1Zero) {
      .left := input.decoded_rs1,
      .right := zeroAddress.output }
    instance (.rs2Zero) {
      .left := input.decoded_rs2,
      .right := zeroAddress.output }
    instance (.rdZero) {
      .left := input.latched_rd,
      .right := zeroAddress.output }
    instance (.rdNonzero) {
      .input := rdZero.result }
    instance (.requestedWrite) {
      .left := input.resetn,
      .right := input.cpuregs_write }
    instance (.enabledWrite) {
      .left := requestedWrite.output,
      .right := rdNonzero.output }
    instance (.rs1Mux) {
      .select := rs1Zero.result,
      .whenFalse := bank[.readValue 0],
      .whenTrue := zeroWord.output }
    instance (.rs2Mux) {
      .select := rs2Zero.result,
      .whenFalse := bank[.readValue 1],
      .whenTrue := zeroWord.output }
  }

end PicoRV
