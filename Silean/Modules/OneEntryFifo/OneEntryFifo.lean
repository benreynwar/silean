import Silean.Authoring.CircuitLogic
import Silean.Authoring.CircuitDescriptionContracts
import Silean.Authoring.CircuitSelection
import Silean.Authoring.FifoPorts
import Silean.Contracts.Fifo.FifoCycleBehavior
import Silean.Interfaces.FifoPorts
import Silean.Modules.EnabledRegister.EnabledRegisterDerived
import Silean.Modules.EnabledResetRegister.EnabledResetRegisterDerived
import Silean.Modules.OneEntryFifo.Control.OneEntryFifoControlDerived
import Silean.Naming.FifoPortsNaming

/-! # One-entry fall-through FIFO

The FIFO forwards an incoming payload combinationally while its single storage
entry is empty. If the consumer stalls, the entry captures that payload; while
occupied, it presents the stored payload until the consumer accepts it.

The authored circuit below shows the control and feedback paths. Its exact
clock-cycle behavior and the laws needed to use that contract are stated in
the same file. Generated structure and certification remain downstream in
`OneEntryFifoDerived.lean`.
-/

namespace Silean.Modules.OneEntryFifo

open Silean
open Silean.Authoring
open Authoring.CircuitDescription
open Contracts.Fifo.Cycle
open Silean.Interfaces.Fifo.ports
open scoped Authoring

abbrev ports := Silean.Interfaces.Fifo.ports
abbrev inputMap := Silean.Interfaces.Fifo.inputMap
abbrev outputMap := Silean.Interfaces.Fifo.outputMap

noncomputable def construction (signalType : SignalType) :
    ModuleBuilder (ports signalType) Unit := do
  let inputValid ← input signalType .inputValid
  let inputData ← input signalType .inputData
  let outputReady ← input signalType .outputReady
  let reset ← input signalType .reset
  wire storedValid : .bit
  wire storedData : signalType
  wire storageUpdate : .bit
  assign storedValid (← Modules.EnabledResetRegister.placeNamed (signalType := .bit)
    "validStorage" false inputValid storageUpdate reset)
  assign storedData (← Modules.EnabledRegister.placeNamed "dataStorage"
    inputData storageUpdate)
  let control ← Modules.OneEntryFifo.Control.place
    storedValid outputReady
  assign storageUpdate control.storageUpdate
  output signalType .outputValid (← storedValid ||| inputValid)
  output signalType .outputData (← mux storedValid inputData storedData)
  output signalType .inputReady control.upstreamReady

noncomputable def description (signalType : SignalType) : Description :=
  ModuleBuilder.build (Naming.FifoPorts.ports signalType)
    (construction signalType)

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

def cycleBehavior (signalType : SignalType) :
    Contracts.Fifo.Cycle.CycleBehavior signalType where
  state := stateMap signalType
  forward := fun inputValid inputData state =>
    (state .storedValid || inputValid,
      bif state .storedValid then state .storedData else inputData)
  ready := fun outputReady state => outputReady || !state .storedValid
  nextState := fun inputs state =>
    let update := (inputs .outputReady && state .storedValid) ||
      (!inputs .outputReady && !state .storedValid)
    fun
      | .storedValid => bif inputs .reset then false
          else bif update then inputs .inputValid else state .storedValid
      | .storedData => bif update then inputs .inputData else state .storedData

abbrev forwardRule (signalType : SignalType) :=
  (cycleBehavior signalType).forwardRule

abbrev readyRule (signalType : SignalType) :=
  (cycleBehavior signalType).readyRule

abbrev stateRule (signalType : SignalType) :=
  (cycleBehavior signalType).stateRule

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
        (bif state .storedValid then state .storedData else inputs .inputData) :=
  (cycleBehavior signalType).forwardRule_holds_iff inputs state outputs

theorem readyRule_holds_iff (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : (cycleContract signalType).state.Values)
    (outputs : (ports signalType).outputs.Values) :
    (readyRule signalType).Holds inputs state outputs ↔
      outputs .inputReady = (inputs .outputReady || !state .storedValid) :=
  (cycleBehavior signalType).readyRule_holds_iff inputs state outputs

section AllowedStep

variable {signalType : SignalType}
  {step : (cycleContract signalType).Step}
  (allowed : (cycleContract signalType).Allows step)

include allowed

/-- Output valid is asserted for either a buffered or incoming payload. -/
theorem outputValid_of_allowed :
    step.outputs .outputValid =
      (step.currentState .storedValid || step.inputs .inputValid) :=
  (forwardRule_holds_iff signalType
    step.inputs step.currentState step.outputs).mp (allowed.1 .forward) |>.1

/-- A buffered payload has priority; otherwise the input falls through. -/
theorem outputData_of_allowed :
    step.outputs .outputData =
      bif step.currentState .storedValid then step.currentState .storedData
      else step.inputs .inputData :=
  (forwardRule_holds_iff signalType
    step.inputs step.currentState step.outputs).mp (allowed.1 .forward) |>.2

/-- The producer may send when the entry is empty or the consumer is ready. -/
theorem inputReady_of_allowed :
    step.outputs .inputReady =
      (step.inputs .outputReady || !step.currentState .storedValid) :=
  (readyRule_holds_iff signalType
    step.inputs step.currentState step.outputs).mp (allowed.1 .ready)

/-- The complete next occupancy equation, including synchronous reset. -/
theorem next_storedValid_of_allowed :
    step.nextState .storedValid =
      bif step.inputs .reset then false else
        bif ((step.inputs .outputReady && step.currentState .storedValid) ||
          (!step.inputs .outputReady && !step.currentState .storedValid))
          then step.inputs .inputValid else step.currentState .storedValid := by
  rw [allowed.2]
  rfl

/-- Payload storage follows the ordinary update condition. Reset clears valid
but does not require choosing or writing a reset payload. -/
theorem next_storedData_of_allowed :
    step.nextState .storedData =
      bif ((step.inputs .outputReady && step.currentState .storedValid) ||
        (!step.inputs .outputReady && !step.currentState .storedValid))
        then step.inputs .inputData else step.currentState .storedData := by
  rw [allowed.2]
  rfl

/-- Reset empties the FIFO regardless of the handshake inputs. -/
theorem next_storedValid_of_reset (reset : step.inputs .reset = true) :
    step.nextState .storedValid = false := by
  rw [next_storedValid_of_allowed allowed, reset]
  rfl

/-- Without an update, the buffered payload is retained. -/
theorem next_storedData_of_no_update
    (noUpdate : ((step.inputs .outputReady && step.currentState .storedValid) ||
      (!step.inputs .outputReady && !step.currentState .storedValid)) = false) :
    step.nextState .storedData = step.currentState .storedData := by
  rw [next_storedData_of_allowed allowed, noUpdate]
  rfl

end AllowedStep

end Silean.Modules.OneEntryFifo
