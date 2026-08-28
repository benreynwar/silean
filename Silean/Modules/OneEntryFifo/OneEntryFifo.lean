import Silean.Modules.EnabledRegister
import Silean.Modules.EnabledResetRegister
import Silean.Interfaces.FifoPorts
import Silean.Modules.Mux
import Silean.Modules.OneEntryFifo.OneEntryFifoControl
import Silean.Contracts.Fifo.FifoCycleBehavior
import Silean.Contracts.Cycle.CycleSchedule
import Silean.Naming.FifoPortsNaming
import Silean.Naming.PrimitiveNaming

namespace Silean.Modules.OneEntryFifo

open Silean
open Contracts.Fifo.Cycle

/-- A one-entry FIFO with combinational fall-through when the entry is empty.
Data is stored only when it cannot pass directly to the output. -/
abbrev ports := Silean.Interfaces.Fifo.ports
abbrev inputMap := Silean.Interfaces.Fifo.inputMap
abbrev outputMap := Silean.Interfaces.Fifo.outputMap

private inductive Instance
  /-- Records whether the storage entry currently contains data. -/
  | validStorage
  /-- Holds the buffered payload. -/
  | dataStorage
  /-- Decides readiness and whether storage must be updated. -/
  | control
  /-- Combines buffered-valid and incoming-valid for `outputValid`. -/
  | outputValidOr
  /-- Selects buffered or incoming data for `outputData`. -/
  | outputDataMux
deriving Enumeration

@[reducible] private def instancePorts (signalType : SignalType) : InstancePorts :=
  EnumeratedMap.of Instance fun
    | .validStorage => EnabledResetRegister.ports .bit
    | .dataStorage => EnabledRegister.ports signalType
    | .control => OneEntryFifo.Control.ports
    | .outputValidOr => Primitives.or.ports
    | .outputDataMux => Mux.ports signalType

@[reducible] private def context (signalType : SignalType) : EndpointContext where
  ports := ports signalType
  instancePorts := instancePorts signalType

private def wiring (signalType : SignalType) :
    Wiring (context signalType).ports (context signalType).instancePorts :=
  let c := context signalType
  { moduleOutput := fun
    -- Boundary outputs are produced by the final output logic.
    | .outputValid => c.instanceOutput .outputValidOr .output
    | .outputData => c.instanceOutput .outputDataMux .result
    | .inputReady => c.instanceOutput .control .upstreamReady
    instanceInput := fun
    -- Update the valid bit when the control logic accepts or removes data.
    | .validStorage, .enable => c.instanceOutput .control .storageUpdate
    | .validStorage, .value => c.moduleInput .inputValid
    | .validStorage, .reset => c.moduleInput .reset
    -- Capture incoming data whenever the entry is updated.
    | .dataStorage, .enable => c.instanceOutput .control .storageUpdate
    | .dataStorage, .value => c.moduleInput .inputData
    -- Readiness depends on the stored-valid bit and downstream readiness.
    | .control, .storedValid => c.instanceOutput .validStorage .value
    | .control, .downstreamReady => c.moduleInput .outputReady
    -- Output is valid when either stored or incoming data is available.
    | .outputValidOr, .left => c.instanceOutput .validStorage .value
    | .outputValidOr, .right => c.moduleInput .inputValid
    -- Prefer buffered data; otherwise allow combinational fall-through.
    | .outputDataMux, .select => c.instanceOutput .validStorage .value
    | .outputDataMux, .whenFalse => c.moduleInput .inputData
    | .outputDataMux, .whenTrue => c.instanceOutput .dataStorage .value }

@[reducible] private def body (signalType : SignalType) : ModuleBody :=
  ⟨context signalType, wiring signalType⟩

@[reducible] private noncomputable def children (signalType : SignalType) :
    Contracts.Cycle.Certification.Children (body signalType)
  | .validStorage => EnabledResetRegister.certified .bit false
  | .dataStorage => EnabledRegister.certified signalType
  | .control => OneEntryFifo.Control.certified
  | .outputValidOr => Primitives.orCertified
  | .outputDataMux => Mux.certified signalType

@[reducible] private noncomputable def childStructure (signalType : SignalType) :=
  Contracts.Cycle.Certification.childStructure (children signalType)

@[reducible] private def structuralChildren (signalType : SignalType) :
    (name : (instancePorts signalType).Name) →
      ModuleStructure ((instancePorts signalType).ports name)
  | .validStorage => EnabledResetRegister.moduleStructure .bit false
  | .dataStorage => EnabledRegister.moduleStructure signalType
  | .control => OneEntryFifo.Control.moduleStructure
  | .outputValidOr => Primitives.orCertified.moduleStructure
  | .outputDataMux => Mux.moduleStructure signalType

def moduleStructure (signalType : SignalType) :
    ModuleStructure (ports signalType) :=
  .composite (body signalType) (structuralChildren signalType)

/-! ## Exact cycle behavior -/

private theorem moduleStructure_eq (signalType : SignalType) :
    moduleStructure signalType =
      Contracts.Cycle.Certification.moduleStructure (body signalType) (children signalType) := by
  unfold moduleStructure Contracts.Cycle.Certification.moduleStructure
  congr
  funext child
  cases child <;> rfl

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
    Contracts.Cycle.CycleOutputRule (ports signalType) (stateMap signalType)
      (.ofLists [.bit, signalType] [.bit, signalType]) where
  readsInputs := ((inputMap signalType).select .inputData).prepend .inputValid
  writesOutputs := ((outputMap signalType).select .outputData).prepend .outputValid
  target
    | (inputValid, (inputData, ())), state =>
        (state .storedValid || inputValid,
          (bif state .storedValid then state .storedData else inputData, ()))

def readyRule (signalType : SignalType) :
    Contracts.Cycle.CycleOutputRule (ports signalType) (stateMap signalType)
    (.ofLists [.bit] [.bit]) where
  readsInputs := (inputMap signalType).select .outputReady
  writesOutputs := (outputMap signalType).select .inputReady
  target
    | (outputReady, ()), state =>
        (outputReady || !state .storedValid, ())

def stateRule (signalType : SignalType) :
    Contracts.Cycle.CycleStateRule (ports signalType) (stateMap signalType) where
  inputTypes := .cons .bit (.cons .bit (.cons .bit (.cons signalType .nil)))
  readsInputs := ((((inputMap signalType).select .inputData).prepend .inputValid).prepend
    .outputReady).prepend .reset
  target
    | (reset, (outputReady, (inputValid, (inputData, ())))), state =>
        let update := (outputReady && state .storedValid) ||
          (!outputReady && !state .storedValid)
        fun
          | .storedValid => bif reset then false
              else bif update then inputValid else state .storedValid
          | .storedData => bif update then inputData else state .storedData

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

def cycleContract (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleContract (ports signalType) where
  state := stateMap signalType
  RuleName := Rule
  ruleNames := inferInstance
  outputRule
    | .forward => ⟨_, forwardRule signalType⟩
    | .ready => ⟨_, readyRule signalType⟩
  stateRule := stateRule signalType
  outputCoverage := by rfl

private abbrev validRule (signalType : SignalType) :
    Contracts.Cycle.Certification.RuleOccurrence (children signalType) :=
  ⟨.validStorage, EnabledResetRegister.Rule.observe⟩
private abbrev dataRule (signalType : SignalType) :
    Contracts.Cycle.Certification.RuleOccurrence (children signalType) :=
  ⟨.dataStorage, EnabledRegister.Rule.observe⟩
private abbrev controlOccurrence (signalType : SignalType) :
    Contracts.Cycle.Certification.RuleOccurrence (children signalType) :=
  ⟨.control, OneEntryFifo.Control.Rule.control⟩
private abbrev validOrRule (signalType : SignalType) :
    Contracts.Cycle.Certification.RuleOccurrence (children signalType) :=
  ⟨.outputValidOr, Primitives.OrRule.apply⟩
private abbrev dataMuxRule (signalType : SignalType) :
    Contracts.Cycle.Certification.RuleOccurrence (children signalType) :=
  ⟨.outputDataMux, Mux.Rule.select⟩

@[simp] private theorem validRule_reads (signalType) : (validRule signalType).reads = [] := rfl
@[simp] private theorem dataRule_reads (signalType) : (dataRule signalType).reads = [] := rfl
@[simp] private theorem controlOccurrence_reads (signalType) :
    (controlOccurrence signalType).reads = [.storedValid, .downstreamReady] := rfl
@[simp] private theorem validOrRule_reads (signalType) :
    (validOrRule signalType).reads = [.left, .right] := rfl
@[simp] private theorem dataMuxRule_reads (signalType) :
    (dataMuxRule signalType).reads = [.select, .whenFalse, .whenTrue] := rfl
@[simp] private theorem validRule_writes (signalType) :
    (validRule signalType).writes = [.value] := rfl
@[simp] private theorem dataRule_writes (signalType) :
    (dataRule signalType).writes = [.value] := rfl
@[simp] private theorem controlOccurrence_writes (signalType) :
    (controlOccurrence signalType).writes = [.upstreamReady, .storageUpdate] := rfl
@[simp] private theorem validOrRule_writes (signalType) :
    (validOrRule signalType).writes = [.output] := rfl
@[simp] private theorem dataMuxRule_writes (signalType) :
    (dataMuxRule signalType).writes = [.result] := rfl

private def forwardSchedule (signalType : SignalType) :
    Contracts.Cycle.Certification.OutputSchedule (body signalType) (children signalType)
      (cycleContract signalType) .forward :=
  .call (validRule signalType)
    (by intro input member; cases member)
    (by simp)
  (.call (dataRule signalType)
    (by intro input member; cases member)
    (by simp)
  (.call (validOrRule signalType)
    (by intro input member
        cases input with
        | left => exact ⟨EnabledResetRegister.Rule.observe, by simp, by simp⟩
        | right => simp [cycleContract, forwardRule, SignalSelection.prepend,
            SignalMap.select, SignalSelection.labels, Contracts.Cycle.Certification.sourceAvailable,
            body, wiring, context, EndpointContext.moduleInput])
    (by simp)
  (.call (dataMuxRule signalType)
    (by intro input member
        cases input with
        | select => exact ⟨EnabledResetRegister.Rule.observe, by simp, by simp⟩
        | whenFalse => simp [cycleContract, forwardRule,
            SignalSelection.prepend, SignalMap.select, SignalSelection.labels,
            Contracts.Cycle.Certification.sourceAvailable, body, wiring, context,
            EndpointContext.moduleInput]
        | whenTrue => exact ⟨EnabledRegister.Rule.observe, by simp, by simp⟩)
    (by simp)
  (.done (by
    intro output member
    cases output with
    | outputValid =>
        change Contracts.Cycle.Certification.outputAvailable
          ([dataMuxRule signalType, validOrRule signalType, dataRule signalType, validRule signalType] :
            Contracts.Cycle.Certification.Availability (children signalType)) Instance.outputValidOr .output
        exact ⟨Primitives.OrRule.apply, by simp, by simp⟩
    | outputData =>
        change Contracts.Cycle.Certification.outputAvailable
          ([dataMuxRule signalType, validOrRule signalType, dataRule signalType, validRule signalType] :
            Contracts.Cycle.Certification.Availability (children signalType)) Instance.outputDataMux .result
        exact ⟨Mux.Rule.select, by simp, by simp⟩
    | inputReady =>
        simp [cycleContract, forwardRule, SignalSelection.prepend,
          SignalMap.select, SignalSelection.labels] at member)))))

private def readySchedule (signalType : SignalType) :
    Contracts.Cycle.Certification.OutputSchedule (body signalType) (children signalType)
      (cycleContract signalType) .ready :=
  .call (validRule signalType)
    (by intro input member; cases member)
    (by simp)
  (.call (controlOccurrence signalType)
    (by intro input member
        cases input with
        | storedValid => exact ⟨EnabledResetRegister.Rule.observe, by simp, by simp⟩
        | downstreamReady => simp [cycleContract, readyRule, SignalMap.select,
            SignalSelection.labels, Contracts.Cycle.Certification.sourceAvailable, body, wiring,
            context, EndpointContext.moduleInput])
    (by simp)
  (.done (by
    intro output member
    cases output with
    | inputReady =>
        change Contracts.Cycle.Certification.outputAvailable
          ([controlOccurrence signalType, validRule signalType] :
            Contracts.Cycle.Certification.Availability (children signalType))
          Instance.control .upstreamReady
        exact ⟨OneEntryFifo.Control.Rule.control, by simp, by simp⟩
    | outputValid | outputData =>
        simp [cycleContract, readyRule, SignalMap.select,
          SignalSelection.labels] at member)))

private def stateSchedule (signalType : SignalType) :
    Contracts.Cycle.Certification.StateSchedule (body signalType) (children signalType) :=
  .call (validRule signalType) (by intro input member; cases member) (by simp)
  (.call (dataRule signalType) (by intro input member; cases member) (by simp)
  (.call (controlOccurrence signalType)
    (by intro input member
        cases input with
        | storedValid => exact ⟨EnabledResetRegister.Rule.observe, by simp, by simp⟩
        | downstreamReady => trivial)
    (by simp)
  (.call (validOrRule signalType)
    (by intro input member
        cases input with
        | left => exact ⟨EnabledResetRegister.Rule.observe, by simp, by simp⟩
        | right => trivial)
    (by simp)
  (.call (dataMuxRule signalType)
    (by intro input member
        cases input with
        | select => exact ⟨EnabledResetRegister.Rule.observe, by simp, by simp⟩
        | whenFalse => trivial
        | whenTrue => exact ⟨EnabledRegister.Rule.observe, by simp, by simp⟩)
    (by simp)
  (.done (by
    intro child input member
    cases child with
    | validStorage =>
        rw [EnabledResetRegister.certified_cycleContract] at member
        cases input with
        | enable => exact ⟨OneEntryFifo.Control.Rule.control, by simp, by simp⟩
        | value | reset => trivial
    | dataStorage =>
        rw [EnabledRegister.certified_cycleContract] at member
        cases input with
        | enable => exact ⟨OneEntryFifo.Control.Rule.control, by simp, by simp⟩
        | value => trivial
    | control =>
        rw [OneEntryFifo.Control.certified_cycleContract] at member
        simp [OneEntryFifo.Control.cycleContract, Contracts.Cycle.CycleStateRule.empty,
          SignalSelection.labels] at member
    | outputValidOr =>
        simp [children, Primitives.orCertified, Primitives.orCycleContract,
          Contracts.Cycle.CycleStateRule.empty, SignalSelection.labels] at member
    | outputDataMux =>
        rw [Mux.certified_cycleContract] at member
        simp [Mux.cycleContract, Mux.stateRule, Contracts.Cycle.CycleStateRule.empty,
          SignalSelection.labels] at member))))))

private def ruleSchedules (signalType : SignalType) :
    Contracts.Cycle.Certification.RuleSchedules (body signalType) (children signalType)
      (cycleContract signalType) where
  output | .forward => forwardSchedule signalType | .ready => readySchedule signalType
  state := stateSchedule signalType

private theorem coversChildren (signalType : SignalType) :
    (ruleSchedules signalType).CoversChildren := by
  intro child rule
  cases child with
  | validStorage =>
    change EnabledResetRegister.Rule at rule
    cases rule
    apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_includes
    change validRule signalType ∈ (stateSchedule signalType).finalAvailability
    simp [stateSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]
  | dataStorage =>
    change EnabledRegister.Rule at rule
    cases rule
    apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_includes
    change dataRule signalType ∈ (stateSchedule signalType).finalAvailability
    simp [stateSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]
  | control =>
    change OneEntryFifo.Control.Rule at rule
    cases rule
    apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_includes
    change controlOccurrence signalType ∈ (stateSchedule signalType).finalAvailability
    simp [stateSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]
  | outputValidOr =>
    change Primitives.OrRule at rule
    cases rule
    apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_includes
    change validOrRule signalType ∈ (stateSchedule signalType).finalAvailability
    simp [stateSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]
  | outputDataMux =>
    change Mux.Rule at rule
    cases rule
    apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_includes
    change dataMuxRule signalType ∈ (stateSchedule signalType).finalAvailability
    simp [stateSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]

private theorem hasAtMostOneSolution (signalType : SignalType) :
    (Contracts.Cycle.Certification.moduleStructure (body signalType)
      (children signalType)).HasAtMostOneSolution :=
  (ruleSchedules signalType).hasAtMostOneSolution (coversChildren signalType)

private def controlInputsFrom (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values) (storedValid : Bool) :
    OneEntryFifo.Control.ports.inputs.Values
  | .storedValid => storedValid
  | .downstreamReady => inputs .outputReady

private def validOrInputsFrom (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values) (storedValid : Bool) :
    Primitives.or.ports.inputs.Values
  | .left => storedValid
  | .right => inputs .inputValid

private def dataMuxInputsFrom (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (storedValid : Bool) (storedData : signalType.Denote) :
    (Mux.ports signalType).inputs.Values
  | .select => storedValid
  | .whenFalse => inputs .inputData
  | .whenTrue => storedData

private noncomputable def validStorageInputs (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (control : ProposedValues (children signalType .control).moduleStructure) :
    (EnabledResetRegister.ports .bit).inputs.Values
  | .value => inputs .inputValid
  | .enable => control.outputs .storageUpdate
  | .reset => inputs .reset

private noncomputable def dataStorageInputs (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (control : ProposedValues (children signalType .control).moduleStructure) :
    (EnabledRegister.ports signalType).inputs.Values
  | .value => inputs .inputData
  | .enable => control.outputs .storageUpdate

private theorem hasStructuralResult (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (currentState : (Contracts.Cycle.Certification.moduleStructure (body signalType)
      (children signalType)).State) :
    ∃ proposal, (Contracts.Cycle.Certification.moduleStructure (body signalType)
      (children signalType)).IsSolution inputs currentState proposal := by
  rcases (children signalType .validStorage).hasCorrespondingState
      (currentState .validStorage) with
    ⟨validContractState, validCorresponds⟩
  rcases (children signalType .dataStorage).hasCorrespondingState
      (currentState .dataStorage) with
    ⟨dataContractState, dataCorresponds⟩
  let storedValid : Bool := validContractState .stored
  let storedData : signalType.Denote := dataContractState .stored
  rcases (children signalType .control).hasStructuralResult
      (controlInputsFrom signalType inputs storedValid) (currentState .control) with
    ⟨control, controlSatisfies⟩
  rcases (children signalType .outputValidOr).hasStructuralResult
      (validOrInputsFrom signalType inputs storedValid) (currentState .outputValidOr) with
    ⟨outputValidOr, validOrSatisfies⟩
  rcases (children signalType .outputDataMux).hasStructuralResult
      (dataMuxInputsFrom signalType inputs storedValid storedData)
      (currentState .outputDataMux) with ⟨outputDataMux, dataMuxSatisfies⟩
  rcases (children signalType .validStorage).hasStructuralResult
      (validStorageInputs signalType inputs control) (currentState .validStorage) with
    ⟨validStorage, validSatisfies⟩
  rcases (children signalType .dataStorage).hasStructuralResult
      (dataStorageInputs signalType inputs control) (currentState .dataStorage) with
    ⟨dataStorage, dataSatisfies⟩
  rcases (children signalType .validStorage).implements
      (validStorageInputs signalType inputs control) validContractState
      (currentState .validStorage) validStorage validCorresponds validSatisfies with
    ⟨validNext, validEvaluates, validNextCorresponds⟩
  rcases (children signalType .dataStorage).implements
      (dataStorageInputs signalType inputs control) dataContractState
      (currentState .dataStorage) dataStorage dataCorresponds dataSatisfies with
    ⟨dataNext, dataEvaluates, dataNextCorresponds⟩
  have validOutput : validStorage.outputs .value = storedValid :=
    (EnabledResetRegister.outputRule_holds_iff .bit _ _ _).mp
      (validEvaluates.1 EnabledResetRegister.Rule.observe)
  have dataOutput : dataStorage.outputs .value = storedData :=
    (EnabledRegister.outputRule_holds_iff signalType _ _ _).mp
      (dataEvaluates.1 EnabledRegister.Rule.observe)
  let childProposals : (name : Instance) → ProposedValues (childStructure signalType name)
    | .validStorage => validStorage
    | .dataStorage => dataStorage
    | .control => control
    | .outputValidOr => outputValidOr
    | .outputDataMux => outputDataMux
  let outputs : (ports signalType).outputs.Values := fun
    | .outputValid => outputValidOr.outputs .output
    | .outputData => outputDataMux.outputs .result
    | .inputReady => control.outputs .upstreamReady
  refine ⟨ProposedValues.composite outputs childProposals, ?_⟩
  constructor
  · intro output; cases output <;> rfl
  · intro child
    cases child with
    | validStorage =>
        change (children signalType .validStorage).moduleStructure.IsSolution
          (ProposedValues.childInputs (body signalType) (childStructure signalType) inputs childProposals
            .validStorage) (currentState .validStorage) validStorage
        rw [show ProposedValues.childInputs (body signalType) (childStructure signalType) inputs
          childProposals .validStorage = validStorageInputs signalType inputs control by
            funext port; cases port <;> rfl]
        exact validSatisfies
    | dataStorage =>
        change (children signalType .dataStorage).moduleStructure.IsSolution
          (ProposedValues.childInputs (body signalType) (childStructure signalType) inputs childProposals
            .dataStorage) (currentState .dataStorage) dataStorage
        rw [show ProposedValues.childInputs (body signalType) (childStructure signalType) inputs
          childProposals .dataStorage = dataStorageInputs signalType inputs control by
            funext port; cases port <;> rfl]
        exact dataSatisfies
    | control =>
        change (children signalType .control).moduleStructure.IsSolution
          (ProposedValues.childInputs (body signalType) (childStructure signalType) inputs childProposals
            .control) (currentState .control) control
        rw [show ProposedValues.childInputs (body signalType) (childStructure signalType) inputs
          childProposals .control = controlInputsFrom signalType inputs storedValid by
            funext port
            cases port with
            | storedValid => exact validOutput
            | downstreamReady => rfl]
        exact controlSatisfies
    | outputValidOr =>
        change (children signalType .outputValidOr).moduleStructure.IsSolution
          (ProposedValues.childInputs (body signalType) (childStructure signalType) inputs childProposals
            .outputValidOr) (currentState .outputValidOr) outputValidOr
        rw [show ProposedValues.childInputs (body signalType) (childStructure signalType) inputs
          childProposals .outputValidOr = validOrInputsFrom signalType inputs storedValid by
            funext port
            cases port with
            | left => exact validOutput
            | right => rfl]
        exact validOrSatisfies
    | outputDataMux =>
        change (children signalType .outputDataMux).moduleStructure.IsSolution
          (ProposedValues.childInputs (body signalType) (childStructure signalType) inputs childProposals
            .outputDataMux) (currentState .outputDataMux) outputDataMux
        rw [show ProposedValues.childInputs (body signalType) (childStructure signalType) inputs
          childProposals .outputDataMux =
            dataMuxInputsFrom signalType inputs storedValid storedData by
          funext port
          cases port with
          | select => exact validOutput
          | whenFalse => rfl
          | whenTrue => exact dataOutput]
        exact dataMuxSatisfies

private def stateCorresponds (signalType : SignalType)
    (contractState : (cycleContract signalType).state.Values)
    (structuralState : (Contracts.Cycle.Certification.moduleStructure (body signalType)
      (children signalType)).State) : Prop :=
  (children signalType .validStorage).stateCorresponds
      (fun | .stored => contractState .storedValid)
      (structuralState .validStorage) ∧
    (children signalType .dataStorage).stateCorresponds
      (fun | .stored => contractState .storedData)
      (structuralState .dataStorage)

theorem forwardRule_holds_iff (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : (cycleContract signalType).state.Values)
    (outputs : (ports signalType).outputs.Values) :
    (forwardRule signalType).Holds inputs state outputs ↔
      outputs .outputValid = (state .storedValid || inputs .inputValid) ∧
      outputs .outputData =
        (bif state .storedValid then state .storedData else inputs .inputData) := by
  simp [Contracts.Cycle.CycleOutputRule.Holds, forwardRule, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select, SignalSelection.prepend]
  intro
  rfl

theorem readyRule_holds_iff (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : (cycleContract signalType).state.Values)
    (outputs : (ports signalType).outputs.Values) :
    (readyRule signalType).Holds inputs state outputs ↔
      outputs .inputReady = (inputs .outputReady || !state .storedValid) := by
  simp [Contracts.Cycle.CycleOutputRule.Holds, readyRule, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select]

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

private theorem implements (signalType : SignalType) :
    Contracts.Cycle.Implements (Contracts.Cycle.Certification.moduleStructure (body signalType)
      (children signalType)) (cycleContract signalType)
      (stateCorresponds signalType) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  let validState : (EnabledResetRegister.cycleContract .bit false).state.Values :=
    fun | .stored => contractState .storedValid
  let dataState : (EnabledRegister.cycleContract signalType).state.Values :=
    fun | .stored => contractState .storedData
  have validCorresponds : (children signalType .validStorage).stateCorresponds
      validState
      (structuralState .validStorage) := corresponds.1
  have dataCorresponds : (children signalType .dataStorage).stateCorresponds
      dataState
      (structuralState .dataStorage) := corresponds.2
  have validMatches := Contracts.Cycle.Certification.childSolutionMatchesContract (children signalType)
    inputs structuralState proposal satisfies .validStorage validState
      validCorresponds
  have dataMatches := Contracts.Cycle.Certification.childSolutionMatchesContract (children signalType)
    inputs structuralState proposal satisfies .dataStorage dataState
      dataCorresponds
  rcases (children signalType .control).hasCorrespondingState
      (structuralState .control) with ⟨controlState, controlCorresponds⟩
  have controlState_eq : controlState = SignalMap.emptyValues := by
    funext statePort
    exact nomatch statePort
  subst controlState
  have controlMatches := Contracts.Cycle.Certification.childSolutionMatchesContract (children signalType)
    inputs structuralState proposal satisfies .control SignalMap.emptyValues
      controlCorresponds
  have validOrMatches := Contracts.Cycle.Certification.childSolutionMatchesContract (children signalType)
    inputs structuralState proposal satisfies .outputValidOr SignalMap.emptyValues
      (by trivial)
  rcases (children signalType .outputDataMux).hasCorrespondingState
      (structuralState .outputDataMux) with ⟨muxState, muxCorresponds⟩
  have muxState_eq : muxState = SignalMap.emptyValues := by
    funext statePort
    exact nomatch statePort
  subst muxState
  have muxMatches := Contracts.Cycle.Certification.childSolutionMatchesContract (children signalType)
    inputs structuralState proposal satisfies .outputDataMux SignalMap.emptyValues
      muxCorresponds
  have boundary := satisfies.1
  rcases proposal with ⟨outputs, childValues⟩
  let validInputs := ProposedValues.childInputs (body signalType) (childStructure signalType) inputs childValues
    Instance.validStorage
  let dataInputs := ProposedValues.childInputs (body signalType) (childStructure signalType) inputs childValues
    Instance.dataStorage
  let controlInputs := ProposedValues.childInputs (body signalType) (childStructure signalType) inputs childValues
    Instance.control
  let muxInputs := ProposedValues.childInputs (body signalType) (childStructure signalType) inputs childValues
    Instance.outputDataMux
  rcases validMatches with ⟨validEvaluates, validNextCorresponds⟩
  rcases dataMatches with ⟨dataEvaluates, dataNextCorresponds⟩
  rcases controlMatches with ⟨controlEvaluates, _⟩
  rcases validOrMatches with ⟨validOrEvaluates, _⟩
  rcases muxMatches with ⟨muxEvaluates, _⟩
  change (EnabledResetRegister.cycleContract .bit false).EvaluatesTo validInputs validState
    (childValues .validStorage).outputs
    ((EnabledResetRegister.cycleContract .bit false).stateRule.apply validInputs validState)
      at validEvaluates
  change (children signalType .validStorage).stateCorresponds
    ((EnabledResetRegister.cycleContract .bit false).stateRule.apply validInputs validState)
    (childValues .validStorage).nextState at validNextCorresponds
  change (EnabledRegister.cycleContract signalType).EvaluatesTo dataInputs dataState
    (childValues .dataStorage).outputs
    ((EnabledRegister.cycleContract signalType).stateRule.apply dataInputs dataState)
      at dataEvaluates
  change (children signalType .dataStorage).stateCorresponds
    ((EnabledRegister.cycleContract signalType).stateRule.apply dataInputs dataState)
    (childValues .dataStorage).nextState at dataNextCorresponds
  let validNext := (EnabledResetRegister.cycleContract .bit false).stateRule.apply
    validInputs validState
  let dataNext := (EnabledRegister.cycleContract signalType).stateRule.apply
    dataInputs dataState
  refine ⟨(cycleContract signalType).stateRule.apply inputs contractState, ?_, ?_⟩
  · constructor
    · intro name
      cases name
      · change (forwardRule signalType).Holds inputs contractState _
        rw [forwardRule_holds_iff signalType]
        have validEquation := (EnabledResetRegister.outputRule_holds_iff .bit _ _ _).mp
          (validEvaluates.1 EnabledResetRegister.Rule.observe)
        have dataEquation := (EnabledRegister.outputRule_holds_iff signalType _ _ _).mp
          (dataEvaluates.1 EnabledRegister.Rule.observe)
        have muxRule := (Mux.selectRule_holds_iff signalType _ _ _).mp
          (muxEvaluates.1 Mux.Rule.select)
        change (childValues .validStorage).outputs .value =
          contractState .storedValid at validEquation
        change (childValues .dataStorage).outputs .value =
          contractState .storedData at dataEquation
        change (childValues .outputDataMux).outputs .result =
          bif muxInputs .select then muxInputs .whenTrue
            else muxInputs .whenFalse at muxRule
        have outputOr := (Primitives.orOutputRule_holds_iff _ _ _).mp
          (validOrEvaluates.1 Primitives.OrRule.apply)
        have validBoundary : outputs .outputValid =
            (childValues .outputValidOr).outputs .output := by
          simpa [ProposedValues.boundaryOutputsSatisfy, body, wiring, context,
            EndpointContext.instanceOutput, SignalSource.value] using
              boundary Interfaces.Fifo.Output.outputValid
        have dataBoundary : outputs .outputData =
            (childValues .outputDataMux).outputs .result := by
          simpa [ProposedValues.boundaryOutputsSatisfy, body, wiring, context,
            EndpointContext.instanceOutput, SignalSource.value] using
              boundary Interfaces.Fifo.Output.outputData
        have orEquation : (childValues .outputValidOr).outputs .output =
            ((childValues .validStorage).outputs .value || inputs .inputValid) := by
          simpa [ProposedValues.childInputs, body, wiring, context, instancePorts,
            EndpointContext.moduleInput, EndpointContext.instanceOutput,
            SignalSource.value] using outputOr
        have muxEquation : (childValues .outputDataMux).outputs .result =
            bif (childValues .validStorage).outputs .value
              then (childValues .dataStorage).outputs .value
              else inputs .inputData := by
          change (childValues .outputDataMux).outputs .result =
            bif (childValues .validStorage).outputs .value
              then (childValues .dataStorage).outputs .value
              else inputs .inputData at muxRule
          exact muxRule
        constructor
        · exact validBoundary.trans (orEquation.trans
            (congrArg (fun value => value || inputs .inputValid) validEquation))
        · rw [validEquation, dataEquation] at muxEquation
          exact dataBoundary.trans muxEquation
      · change (readyRule signalType).Holds inputs contractState _
        rw [readyRule_holds_iff signalType]
        have controlRule := (OneEntryFifo.Control.controlRule_holds_iff _ _ _).mp
          (controlEvaluates.1 OneEntryFifo.Control.Rule.control)
        have validEquation := (EnabledResetRegister.outputRule_holds_iff .bit _ _ _).mp
          (validEvaluates.1 EnabledResetRegister.Rule.observe)
        change (childValues .validStorage).outputs .value =
          contractState .storedValid at validEquation
        change (childValues .control).outputs .upstreamReady =
            (controlInputs .downstreamReady || !controlInputs .storedValid) ∧
          _ at controlRule
        have readyBoundary : outputs .inputReady =
            (childValues .control).outputs .upstreamReady := by
          simpa [ProposedValues.boundaryOutputsSatisfy, body, wiring, context,
            EndpointContext.instanceOutput, SignalSource.value] using
              boundary Interfaces.Fifo.Output.inputReady
        have readyEquation : (childValues .control).outputs .upstreamReady =
            (inputs .outputReady || !(childValues .validStorage).outputs .value) := by
          have downstream : controlInputs .downstreamReady = inputs .outputReady := by
            simp [controlInputs, ProposedValues.childInputs, body, wiring,
              context, instancePorts, EndpointContext.moduleInput,
              EndpointContext.instanceOutput, SignalSource.value]
          have stored : controlInputs .storedValid =
              (childValues .validStorage).outputs .value := by
            simp [controlInputs, ProposedValues.childInputs, body, wiring,
              context, instancePorts, EndpointContext.moduleInput,
              EndpointContext.instanceOutput, SignalSource.value]
          rw [downstream, stored] at controlRule
          exact controlRule.1
        rw [validEquation] at readyEquation
        exact readyBoundary.trans readyEquation
    · rfl
  · have controlRule := (OneEntryFifo.Control.controlRule_holds_iff _ _ _).mp
      (controlEvaluates.1 OneEntryFifo.Control.Rule.control)
    have validOutputRule :=
      (EnabledResetRegister.outputRule_holds_iff .bit _ _ _).mp
        (validEvaluates.1 EnabledResetRegister.Rule.observe)
    change (childValues .validStorage).outputs .value =
      contractState .storedValid at validOutputRule
    change _ ∧ (childValues .control).outputs .storageUpdate =
      ((controlInputs .downstreamReady && controlInputs .storedValid) ||
        (!controlInputs .downstreamReady && !controlInputs .storedValid)) at controlRule
    have updateEquation := controlRule.2
    change (childValues .control).outputs .storageUpdate =
      ((inputs .outputReady && (childValues .validStorage).outputs .value) ||
        (!inputs .outputReady && !(childValues .validStorage).outputs .value)) at updateEquation
    rw [validOutputRule] at updateEquation
    have validNextEquation : validNext .stored =
        bif validInputs .reset then false
        else bif validInputs .enable then validInputs .value else validState .stored := by
      rfl
    have dataNextEquation : dataNext .stored =
        bif dataInputs .enable then dataInputs .value else dataState .stored := by
      rfl
    let nextValidState : (EnabledResetRegister.cycleContract .bit false).state.Values :=
      fun | .stored => (cycleContract signalType).stateRule.apply inputs contractState .storedValid
    let nextDataState : (EnabledRegister.cycleContract signalType).state.Values :=
      fun | .stored => (cycleContract signalType).stateRule.apply inputs contractState .storedData
    have validNextEq : nextValidState = validNext := by
      funext statePort
      cases statePort
      rw [validNextEquation]
      simp [validInputs, ProposedValues.childInputs, body, wiring, context,
        instancePorts, EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value, validState]
      cases resetValue : inputs .reset
      · simp [nextValidState, cycleContract, stateRule_apply_storedValid,
          resetValue]
        exact congrArg
          (fun update => bif update then inputs .inputValid
            else contractState .storedValid) updateEquation.symm
      · simp [nextValidState, cycleContract, stateRule_apply_storedValid,
          resetValue]
    have dataNextEq : nextDataState = dataNext := by
      funext statePort
      cases statePort
      rw [dataNextEquation]
      simp [dataInputs, ProposedValues.childInputs, body, wiring, context,
        instancePorts, EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value, dataState]
      exact congrArg
        (fun update => bif update then inputs .inputData
          else contractState .storedData) updateEquation.symm
    change (children signalType .validStorage).stateCorresponds
        nextValidState
        (childValues .validStorage).nextState ∧
      (children signalType .dataStorage).stateCorresponds
        nextDataState
        (childValues .dataStorage).nextState
    constructor
    · rw [validNextEq]
      exact validNextCorresponds
    · rw [dataNextEq]
      exact dataNextCorresponds

private noncomputable def proofCertification (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleCertification
      (Contracts.Cycle.Certification.moduleStructure (body signalType) (children signalType))
      (cycleContract signalType) where
  stateCorresponds := stateCorresponds signalType
  hasCorrespondingState := fun structuralState => by
    rcases (children signalType .validStorage).hasCorrespondingState
        (structuralState .validStorage) with ⟨validState, validCorresponds⟩
    rcases (children signalType .dataStorage).hasCorrespondingState
        (structuralState .dataStorage) with ⟨dataState, dataCorresponds⟩
    exact ⟨(fun
      | .storedValid => validState .stored
      | .storedData => dataState .stored), ⟨validCorresponds, dataCorresponds⟩⟩
  hasStructuralResult := hasStructuralResult signalType
  structuralResultUnique := hasAtMostOneSolution signalType
  implements := implements signalType

noncomputable opaque certification (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure signalType)
      (cycleContract signalType) :=
  (proofCertification signalType).transportStructure
    (moduleStructure_eq signalType).symm

noncomputable def certified (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleCertified (ports signalType) :=
  (certification signalType).bundle

@[simp] theorem certified_cycleContract (signalType : SignalType) :
    (certified signalType).cycleContract = cycleContract signalType := rfl

theorem hasExactlyOneSolution (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (currentState : (moduleStructure signalType).State) :
    ∃ proposal, (moduleStructure signalType).IsSolution inputs currentState proposal ∧
      ∀ other, (moduleStructure signalType).IsSolution inputs currentState other →
        other = proposal :=
  (certified signalType).hasExactlyOneStructuralResult inputs currentState

end Silean.Modules.OneEntryFifo

namespace Silean.Modules.OneEntryFifo.Naming

open Silean Silean.Naming

def namingWith (signalType : SignalType) (typeNaming : SignalTypeNaming signalType) :
    ModuleNaming (Modules.OneEntryFifo.moduleStructure signalType) := by
  unfold Modules.OneEntryFifo.moduleStructure
  exact .composite ⟨"one_entry_fifo", "structural", [.shape signalType]⟩
    (Silean.Naming.FifoPorts.portsWithNaming signalType typeNaming)
    (fun
      | .validStorage => "valid_storage"
      | .dataStorage => "data_storage"
      | .control => "control"
      | .outputValidOr => "output_valid_or"
      | .outputDataMux => "output_data_mux")
    (fun
      | .validStorage => Modules.EnabledResetRegister.Naming.naming .bit false
      | .dataStorage => Modules.EnabledRegister.Naming.namingWith signalType typeNaming
      | .control => Modules.OneEntryFifo.Control.Naming.naming
      | .outputValidOr => Silean.Naming.Primitive.or
      | .outputDataMux => Modules.Mux.Naming.namingWith signalType typeNaming)

def naming (signalType : SignalType) :
    ModuleNaming (Modules.OneEntryFifo.moduleStructure signalType) :=
  namingWith signalType (.positional signalType)

end Silean.Modules.OneEntryFifo.Naming
