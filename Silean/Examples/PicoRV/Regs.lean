import Silean.Foundation.BitVector
import Silean.ModuleCycleContract
import Silean.ModuleCycleEvaluation

namespace Silean.Examples.PicoRV.Regs

open Silean

abbrev Word := Fin 32 → Bool
abbrev RegisterAddress := Fin 5 → Bool
abbrev RegisterValues := Fin 32 → Word

inductive Input
  | resetn
  | decoded_rs1
  | decoded_rs2
  | cpuregs_write
  | latched_rd
  | cpuregs_wrdata
deriving Enumeration

inductive Output
  | cpuregs_rs1
  | cpuregs_rs2
deriving Enumeration

@[reducible] def inputMap : SignalMap :=
  EnumeratedMap.of Input fun
    | .resetn | .cpuregs_write => .bit
    | .decoded_rs1 | .decoded_rs2 | .latched_rd => .vector 5 .bit
    | .cpuregs_wrdata => .vector 32 .bit

@[reducible] def outputMap : SignalMap :=
  EnumeratedMap.of Output fun
    | .cpuregs_rs1 | .cpuregs_rs2 => .vector 32 .bit

@[reducible] def ports : ModulePorts := ⟨inputMap, outputMap⟩

inductive State | cpuregs
deriving Enumeration

@[reducible] def stateMap : SignalMap :=
  EnumeratedMap.of State fun
    | .cpuregs => .vector 32 (.vector 32 .bit)

def zeroWord : Word := fun _ => false

def registerIndex (address : RegisterAddress) : Fin 32 :=
  BitVector.toIndex 5 address

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

inductive Rule
  | cpuregs_rs1
  | cpuregs_rs2
deriving Enumeration

def cpuregsRs1Rule :
    CycleOutputRule ports stateMap
      { inputTypes := .cons (.vector 5 .bit) .nil
        outputTypes := .cons (.vector 32 .bit) .nil } where
  readsInputs := inputMap.select .decoded_rs1
  writesOutputs := outputMap.select .cpuregs_rs1
  target
    | (decoded_rs1, ()), state =>
        (readRegister decoded_rs1 (state .cpuregs), ())

def cpuregsRs2Rule :
    CycleOutputRule ports stateMap
      { inputTypes := .cons (.vector 5 .bit) .nil
        outputTypes := .cons (.vector 32 .bit) .nil } where
  readsInputs := inputMap.select .decoded_rs2
  writesOutputs := outputMap.select .cpuregs_rs2
  target
    | (decoded_rs2, ()), state =>
        (readRegister decoded_rs2 (state .cpuregs), ())

def stateRule : CycleStateRule ports stateMap where
  inputTypes := .cons .bit
    (.cons .bit (.cons (.vector 5 .bit) (.cons (.vector 32 .bit) .nil)))
  readsInputs := ((((inputMap.select .cpuregs_wrdata).prepend .latched_rd).prepend
    .cpuregs_write).prepend .resetn)
  target
    | (resetn, (cpuregs_write, (latched_rd, (cpuregs_wrdata, ())))), state =>
        fun
          | .cpuregs => nextRegisters resetn cpuregs_write latched_rd
              cpuregs_wrdata (state .cpuregs)

@[reducible] def cycleContract : ModuleCycleContract ports where
  state := stateMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule
    | .cpuregs_rs1 => ⟨_, cpuregsRs1Rule⟩
    | .cpuregs_rs2 => ⟨_, cpuregsRs2Rule⟩
  stateRule := stateRule
  outputCoverage := by rfl

@[simp] theorem readRegister_zero (registers : RegisterValues) :
    readRegister (fun _ => false) registers = zeroWord := by
  have zeroIndex : registerIndex (fun _ => false) = 0 := by
    apply Fin.ext
    simp [registerIndex, BitVector.toIndex_val]
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
  simp [cpuregsRs1Rule, CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select]

@[simp] theorem cpuregsRs2Rule_holds_iff
    (inputs : ports.inputs.Values) (state : stateMap.Values)
    (outputs : ports.outputs.Values) :
    cpuregsRs2Rule.Holds inputs state outputs ↔
      outputs .cpuregs_rs2 = readRegister (inputs .decoded_rs2) (state .cpuregs) := by
  simp [cpuregsRs2Rule, CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select]

end Silean.Examples.PicoRV.Regs
