import Silean.Authoring.ModuleCycleContract
import Silean.Authoring.ModuleDesign
import Silean.Contracts.Fifo.FifoCycleBehavior
import Silean.Interfaces.FifoPorts
import Silean.Modules.EnabledRegister.EnabledRegister
import Silean.Modules.EnabledResetRegister.EnabledResetRegister
import Silean.Modules.Mux.Mux
import Silean.Modules.OneEntryFifo.Control.OneEntryFifoControl
import Silean.Naming.FifoPortsNaming
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.OrPrimitive

namespace Silean.Modules

open Silean
open Silean.Authoring

/-! A one-entry FIFO with combinational fall-through when the entry is empty.
Data is stored only when it cannot pass directly to the output. -/

module_design OneEntryFifo (signalType : SignalType) where
  boundary (Interfaces.Fifo.ports signalType)
    (naming := Naming.FifoPorts.ports signalType)
  instances {
    -- Records whether the storage entry currently contains data.
    validStorage := EnabledResetRegister.design .bit false,
    -- Holds the buffered payload.
    dataStorage := EnabledRegister.design signalType,
    -- Decides readiness and whether storage must be updated.
    control := OneEntryFifo.Control.design,
    -- Combines buffered-valid and incoming-valid for the output.
    outputValidOr := Primitives.orDesign,
    -- Selects buffered or incoming data.
    outputDataMux := Mux.design signalType }
  wiring {
    outputs {
      .outputValid := outputValidOr.output,
      .outputData := outputDataMux.result,
      .inputReady := control.upstreamReady }
    instance (.validStorage) {
      .enable := control.storageUpdate,
      .value := input.inputValid,
      .reset := input.reset }
    instance (.dataStorage) {
      .enable := control.storageUpdate,
      .data := input.inputData }
    instance (.control) {
      .storedValid := validStorage.value,
      .downstreamReady := input.outputReady }
    instance (.outputValidOr) {
      .left := validStorage.value,
      .right := input.inputValid }
    instance (.outputDataMux) {
      .select := validStorage.value,
      .whenFalse := input.inputData,
      .whenTrue := dataStorage.q }
  }

end Silean.Modules

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

theorem next_storedValid_of_reset (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : (stateMap signalType).Values) (reset : inputs .reset = true) :
    (stateRule signalType).apply inputs state .storedValid = false := by
  simp [reset]

/-- Payload storage follows the ordinary FIFO update condition even during a
reset. In particular, reset does not require choosing or writing a reset
payload. -/
theorem next_storedData_of_no_update (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : (stateMap signalType).Values)
    (noUpdate : ((inputs .outputReady && state .storedValid) ||
      (!inputs .outputReady && !state .storedValid)) = false) :
    (stateRule signalType).apply inputs state .storedData = state .storedData := by
  simp [noUpdate]

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

@[simp] theorem evaluate_outputValid (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : (cycleContract signalType).state.Values) :
    ((cycleContract signalType).evaluate inputs state).1 .outputValid =
      (state .storedValid || inputs .inputValid) := rfl

@[simp] theorem evaluate_outputData (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : (cycleContract signalType).state.Values) :
    ((cycleContract signalType).evaluate inputs state).1 .outputData =
      bif state .storedValid then state .storedData else inputs .inputData := rfl

@[simp] theorem evaluate_inputReady (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : (cycleContract signalType).state.Values) :
    ((cycleContract signalType).evaluate inputs state).1 .inputReady =
      (inputs .outputReady || !state .storedValid) := rfl

@[simp] theorem evaluate_next_storedValid (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : (cycleContract signalType).state.Values) :
    ((cycleContract signalType).evaluate inputs state).2 .storedValid =
      (stateRule signalType).apply inputs state .storedValid := rfl

@[simp] theorem evaluate_next_storedData (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : (cycleContract signalType).state.Values) :
    ((cycleContract signalType).evaluate inputs state).2 .storedData =
      (stateRule signalType).apply inputs state .storedData := rfl

end Silean.Modules.OneEntryFifo
