import Silean.Foundation.BitVector
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.CircuitDescription
import Silean.Authoring.ModulePorts
import Silean.Contracts.Cycle.CycleEvaluation
import PicoRV.Authoring.CircuitLogic
import Silean.Modules.RegisterBank.RegisterBankDerived

namespace PicoRV.Regs

open Silean
open Silean.Authoring
open Authoring.CircuitDescription
open scoped Authoring

/-! PicoRV32's 32-entry integer register file. Register zero always reads as
zero and ignores writes. -/

abbrev Word := Fin 32 → Bool
abbrev RegisterAddress := Fin 5 → Bool

module_ports ports where
  input resetn : .bit,
  input decoded_rs1 : .vector 5 .bit,
  input decoded_rs2 : .vector 5 .bit,
  input cpuregs_write : .bit,
  input latched_rd : .vector 5 .bit,
  input cpuregs_wrdata : .vector 32 .bit,
  output cpuregs_rs1 : .vector 32 .bit,
  output cpuregs_rs2 : .vector 32 .bit

abbrev wordType : SignalType := .vector 32 .bit
abbrev addressType : SignalType := .vector 5 .bit
def zeroAddressValue : addressType.Denote := fun _ => false
def zeroWordValue : wordType.Denote := fun _ => false

abbrev RegisterValues := Fin 32 → Word

open PicoRV.Authoring
open ports

noncomputable def construction : ModuleBuilder ports Unit := do
  let resetn ← input .resetn
  let decodedRs1 ← input .decoded_rs1
  let decodedRs2 ← input .decoded_rs2
  let cpuregsWrite ← input .cpuregs_write
  let latchedRd ← input .latched_rd
  let cpuregsWrdata ← input .cpuregs_wrdata

  let zeroAddress ← constant addressType zeroAddressValue
  let zeroWord ← constant wordType zeroWordValue
  let rdNonzero ← !! (← latchedRd === zeroAddress)
  let writeEnable ← (← resetn &&& cpuregsWrite) &&& rdNonzero
  let bank ← Silean.Modules.RegisterBank.place
    (element := wordType) (addressWidth := 5) (readCount := 2)
    writeEnable latchedRd cpuregsWrdata fun
      | 0 => decodedRs1
      | 1 => decodedRs2

  output .cpuregs_rs1
    (← mux (← decodedRs1 === zeroAddress) (bank.readValue 0) zeroWord)
  output .cpuregs_rs2
    (← mux (← decodedRs2 === zeroAddress) (bank.readValue 1) zeroWord)

noncomputable def description : Description :=
  ModuleBuilder.build Naming.ports construction

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

module_cycle_contract cycleContract for ports where
  state := stateMap
  output_rule cpuregs_rs1 where
    reads := [decoded_rs1]
    writes := {
      cpuregs_rs1 := readRegister decoded_rs1 (state .cpuregs) }
  output_rule cpuregs_rs2 where
    reads := [decoded_rs2]
    writes := {
      cpuregs_rs2 := readRegister decoded_rs2 (state .cpuregs) }
  state_rule where
    reads := [resetn, cpuregs_write, latched_rd, cpuregs_wrdata]
    next := {
      cpuregs := nextRegisters resetn cpuregs_write latched_rd cpuregs_wrdata
        (state .cpuregs) }

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

section AllowedStep

variable {step : cycleContract.Step} (allowed : cycleContract.Allows step)

include allowed

/-- The first read port returns register zero as zero and otherwise reads the
selected architectural register. -/
theorem cpuregs_rs1_of_allowed :
    step.outputs .cpuregs_rs1 =
      readRegister (step.inputs .decoded_rs1) (step.currentState .cpuregs) :=
  cycleContract.cpuregs_rs1 allowed

/-- The second read port follows the same architectural register-zero rule. -/
theorem cpuregs_rs2_of_allowed :
    step.outputs .cpuregs_rs2 =
      readRegister (step.inputs .decoded_rs2) (step.currentState .cpuregs) :=
  cycleContract.cpuregs_rs2 allowed

/-- The complete register array advances according to the write/reset rule. -/
theorem next_cpuregs_of_allowed :
    step.nextState .cpuregs =
      nextRegisters (step.inputs .resetn) (step.inputs .cpuregs_write)
        (step.inputs .latched_rd) (step.inputs .cpuregs_wrdata)
        (step.currentState .cpuregs) := by
  rw [allowed.2]
  rfl

end AllowedStep

end PicoRV.Regs
