import Silean.Foundation.BitVector
import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.CircuitDescription
import Silean.Contracts.Cycle.CycleEvaluation
import PicoRV.Authoring.CircuitLogic
import PicoRV.Internal.RegsStructure
import Silean.Modules.RegisterBank.RegisterBank

namespace PicoRV.Regs

open Silean
open Silean.Authoring

/-! PicoRV32's 32-entry integer register file. Register zero always reads as
zero and ignores writes. The exact cycle contract is followed by a structural
implementation around the generic two-read `RegisterBank`. -/

abbrev RegisterValues := Fin 32 → Word

/-! ## Authored hardware -/

namespace Description

open Silean.Authoring.CircuitDescription
open PicoRV.Authoring
open scoped Silean.Authoring

noncomputable def construction : Builder Unit := do
  let resetn ← input "resetn" .bit
  let decodedRs1 ← input "decoded_rs1" addressType
  let decodedRs2 ← input "decoded_rs2" addressType
  let cpuregsWrite ← input "cpuregs_write" .bit
  let latchedRd ← input "latched_rd" addressType
  let cpuregsWrdata ← input "cpuregs_wrdata" wordType

  let zeroAddress ← constant addressType zeroAddressValue
  let zeroWord ← constant wordType zeroWordValue
  let rdNonzero ← !! (← latchedRd === zeroAddress)
  let writeEnable ← (← resetn &&& cpuregsWrite) &&& rdNonzero
  let bank ← Silean.Modules.RegisterBank.place
    (element := wordType) (addressWidth := 5) (readCount := 2)
    writeEnable latchedRd cpuregsWrdata fun
      | 0 => decodedRs1
      | 1 => decodedRs2

  output "cpuregs_rs1"
    (← mux (← decodedRs1 === zeroAddress) (bank.readValue 0) zeroWord)
  output "cpuregs_rs2"
    (← mux (← decodedRs2 === zeroAddress) (bank.readValue 1) zeroWord)

noncomputable def description : Description :=
  build construction

end Description

/-! ## Placement -/

structure PlacedOutputs where
  cpuregsRs1 : Authoring.CircuitDescription.Net wordType
  cpuregsRs2 : Authoring.CircuitDescription.Net wordType

noncomputable def placeNamed (name : Naming.SourceName)
    (resetn : Authoring.CircuitDescription.Net .bit)
    (decodedRs1 decodedRs2 : Authoring.CircuitDescription.Net addressType)
    (cpuregsWrite : Authoring.CircuitDescription.Net .bit)
    (latchedRd : Authoring.CircuitDescription.Net addressType)
    (cpuregsWrdata : Authoring.CircuitDescription.Net wordType) :
    Authoring.CircuitDescription.Builder PlacedOutputs := do
  let child ← Authoring.CircuitDescription.placeNamed name design fun
    | .resetn => resetn
    | .decoded_rs1 => decodedRs1
    | .decoded_rs2 => decodedRs2
    | .cpuregs_write => cpuregsWrite
    | .latched_rd => latchedRd
    | .cpuregs_wrdata => cpuregsWrdata
  pure { cpuregsRs1 := child .cpuregs_rs1, cpuregsRs2 := child .cpuregs_rs2 }

noncomputable def place
    (resetn : Authoring.CircuitDescription.Net .bit)
    (decodedRs1 decodedRs2 : Authoring.CircuitDescription.Net addressType)
    (cpuregsWrite : Authoring.CircuitDescription.Net .bit)
    (latchedRd : Authoring.CircuitDescription.Net addressType)
    (cpuregsWrdata : Authoring.CircuitDescription.Net wordType) :
    Authoring.CircuitDescription.Builder PlacedOutputs := do
  let child ← Authoring.CircuitDescription.placeIndexed "regs" design fun
    | .resetn => resetn
    | .decoded_rs1 => decodedRs1
    | .decoded_rs2 => decodedRs2
    | .cpuregs_write => cpuregsWrite
    | .latched_rd => latchedRd
    | .cpuregs_wrdata => cpuregsWrdata
  pure { cpuregsRs1 := child .cpuregs_rs1, cpuregsRs2 := child .cpuregs_rs2 }

attribute [circuit_description] placeNamed place

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

end PicoRV.Regs
