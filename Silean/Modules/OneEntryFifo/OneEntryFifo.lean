import Silean.Authoring.CircuitDescription
import Silean.Authoring.ModuleCycleContract
import Silean.Contracts.Fifo.FifoCycleBehavior
import Silean.Interfaces.FifoPorts
import Silean.Modules.OneEntryFifo.Internal.OneEntryFifoStructure
import Silean.Naming.FifoPortsNaming
import Silean.Primitives.Or

/-! # One-entry fall-through FIFO

The FIFO forwards an incoming payload combinationally while its single storage
entry is empty. If the consumer stalls, the entry captures that payload; while
occupied, it presents the stored payload until the consumer accepts it.

The authored circuit below shows the control and feedback paths. Its exact
clock-cycle behavior is stated later in this file. The separate higher-level
FIFO refinement is intentionally kept in `OneEntryFifoFifoTheorems.lean`.
-/

namespace Silean.Modules.OneEntryFifo.Description

open Silean
open Silean.Authoring.CircuitDescription

noncomputable def construction (signalType : SignalType) : Builder Unit := do
  let inputValid ← input "input_valid" .bit
  let inputData ← input "input_data" signalType
  let outputReady ← input "output_ready" .bit
  let reset ← input "reset" .bit
  let storedValid ← wire "stored_valid" .bit
  let storedData ← wire "stored_data" signalType
  let storageUpdate ← wire "storage_update" .bit
  let valid ← Modules.EnabledResetRegister.placeNamed (signalType := .bit)
    "validStorage" false inputValid storageUpdate reset
  let data ← Modules.EnabledRegister.placeNamed "dataStorage"
    inputData storageUpdate
  let (inputReady, update) ← Modules.OneEntryFifo.Control.placeNamed
    "control" storedValid outputReady
  let outputValid ← Primitives.Or.placeNamed "outputValidOr"
    storedValid inputValid
  let outputData ← Modules.Mux.placeNamed "outputDataMux"
    storedValid inputData storedData
  assign storedValid valid
  assign storedData data
  assign storageUpdate update
  output "output_valid" outputValid
  output "output_data" outputData
  output "input_ready" inputReady

noncomputable def description (signalType : SignalType) : Description :=
  build (construction signalType)

end Silean.Modules.OneEntryFifo.Description

namespace Silean.Modules.OneEntryFifo

open Silean
open Contracts.Fifo.Cycle
open Silean.Authoring

abbrev ports := Silean.Interfaces.Fifo.ports
abbrev inputMap := Silean.Interfaces.Fifo.inputMap
abbrev outputMap := Silean.Interfaces.Fifo.outputMap

def namingWith (signalType : SignalType)
    (typeNaming : Silean.Naming.SignalTypeNaming signalType) :
    Silean.Naming.ModuleNaming (moduleStructure signalType) :=
  (naming signalType).withPorts
    (Silean.Naming.FifoPorts.portsWithNaming signalType typeNaming)

/-! ## Placement -/

/-- Boundary nets returned when a one-entry FIFO is placed as a child. -/
structure PlacedOutputs (signalType : SignalType) where
  outputValid : Authoring.CircuitDescription.Net .bit
  outputData : Authoring.CircuitDescription.Net signalType
  inputReady : Authoring.CircuitDescription.Net .bit

/-- Place a one-entry FIFO under a caller-chosen instance name. -/
noncomputable def placeNamed (name : Silean.Naming.SourceName)
    (inputValid : Authoring.CircuitDescription.Net .bit)
    (inputData : Authoring.CircuitDescription.Net signalType)
    (outputReady reset : Authoring.CircuitDescription.Net .bit) :
    Authoring.CircuitDescription.Builder (PlacedOutputs signalType) := do
  let child ← Authoring.CircuitDescription.placeNamed name (design signalType) fun
    | .inputValid => inputValid
    | .inputData => inputData
    | .outputReady => outputReady
    | .reset => reset
  pure {
    outputValid := child .outputValid
    outputData := child .outputData
    inputReady := child .inputReady }

/-! ## Exact cycle behavior -/

inductive State
  /-- Whether the single storage entry contains valid data. -/
  | storedValid
  /-- The payload held in the storage entry. -/
  | storedData
deriving Enumeration

def stateMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of State fun
    | .storedValid => .bit
    | .storedData => signalType

def forwardRule (signalType : SignalType) :
    Contracts.Cycle.CycleOutputRule (ports signalType) (stateMap signalType) where
  readsInputs := Contracts.Fifo.Cycle.CycleBehavior.forwardInputGroup signalType
  writesOutputs := Contracts.Fifo.Cycle.CycleBehavior.forwardOutputGroup signalType
  target inputs state := fun
    | .outputValid => state .storedValid || inputs .inputValid
    | .outputData => bif state .storedValid then state .storedData else inputs .inputData

def readyRule (signalType : SignalType) :
    Contracts.Cycle.CycleOutputRule (ports signalType) (stateMap signalType) where
  readsInputs := Contracts.Fifo.Cycle.CycleBehavior.readyInputGroup signalType
  writesOutputs := Contracts.Fifo.Cycle.CycleBehavior.readyOutputGroup signalType
  target inputs state := fun
    | .inputReady => inputs .outputReady || !state .storedValid

def stateRule (signalType : SignalType) :
    Contracts.Cycle.CycleStateRule (ports signalType) (stateMap signalType) where
  readsInputs := .all (inputMap signalType)
  target inputs state :=
    let update := (inputs .outputReady && state .storedValid) ||
      (!inputs .outputReady && !state .storedValid)
    fun
      | .storedValid => bif inputs .reset then false
          else bif update then inputs .inputValid else state .storedValid
      | .storedData => bif update then inputs .inputData else state .storedData

def cycleBehavior (signalType : SignalType) :
    Contracts.Fifo.Cycle.CycleBehavior signalType where
  state := stateMap signalType
  forward := fun inputValid inputData state =>
    (state .storedValid || inputValid,
      bif state .storedValid then state .storedData else inputData)
  ready := fun outputReady state => outputReady || !state .storedValid
  nextState := (stateRule signalType).apply

def cycleContract (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleContract (ports signalType) :=
  (cycleBehavior signalType).cycleContract

@[simp] theorem stateRule_apply_storedValid (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : (stateMap signalType).Values) :
    (stateRule signalType).apply inputs state .storedValid =
      bif inputs .reset then false else
        bif ((inputs .outputReady && state .storedValid) ||
          (!inputs .outputReady && !state .storedValid))
          then inputs .inputValid else state .storedValid := rfl

@[simp] theorem stateRule_apply_storedData (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : (stateMap signalType).Values) :
    (stateRule signalType).apply inputs state .storedData =
      bif ((inputs .outputReady && state .storedValid) ||
        (!inputs .outputReady && !state .storedValid))
        then inputs .inputData else state .storedData := rfl

theorem forwardRule_holds_iff (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : (cycleContract signalType).state.Values)
    (outputs : (ports signalType).outputs.Values) :
    (forwardRule signalType).Holds inputs state outputs ↔
      outputs .outputValid = (state .storedValid || inputs .inputValid) ∧
      outputs .outputData =
        (bif state .storedValid then state .storedData else inputs .inputData) := by
  unfold forwardRule Contracts.Cycle.CycleOutputRule.Holds SignalGroup.Matches
  constructor
  · intro equal
    exact ⟨congrFun equal .outputValid, congrFun equal .outputData⟩
  · rintro ⟨valid, data⟩
    funext output
    cases output <;> assumption

theorem readyRule_holds_iff (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : (cycleContract signalType).state.Values)
    (outputs : (ports signalType).outputs.Values) :
    (readyRule signalType).Holds inputs state outputs ↔
      outputs .inputReady = (inputs .outputReady || !state .storedValid) := by
  unfold readyRule Contracts.Cycle.CycleOutputRule.Holds SignalGroup.Matches
  constructor
  · intro equal
    exact congrFun equal .inputReady
  · intro equal
    funext output
    cases output
    exact equal

end Silean.Modules.OneEntryFifo
