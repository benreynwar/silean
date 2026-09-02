import Silean.Modules.EnabledRegister
import Silean.Modules.EnabledResetRegister
import Silean.Interfaces.FifoPorts
import Silean.Modules.Mux
import Silean.Modules.OneEntryFifo.OneEntryFifoControl
import Silean.Contracts.Fifo.FifoCycleBehavior
import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation
import Silean.Naming.FifoPortsNaming
import Silean.Naming.PrimitiveNaming

namespace Silean.Modules.OneEntryFifo

open Silean
open Contracts.Fifo.Cycle
open Contracts.Cycle.Certification.Layer

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

@[reducible] private def childContracts (signalType : SignalType) :
    Contracts.Cycle.ChildCycleContracts (body signalType)
  | .validStorage => EnabledResetRegister.cycleContract .bit false
  | .dataStorage => EnabledRegister.cycleContract signalType
  | .control => OneEntryFifo.Control.cycleContract
  | .outputValidOr => Primitives.orCycleContract
  | .outputDataMux => Mux.cycleContract signalType

private abbrev validRule (signalType : SignalType) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body signalType) (childContracts signalType) :=
  ⟨.validStorage, EnabledResetRegister.Rule.observe⟩
private abbrev dataRule (signalType : SignalType) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body signalType) (childContracts signalType) :=
  ⟨.dataStorage, EnabledRegister.Rule.observe⟩
private abbrev controlOccurrence (signalType : SignalType) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body signalType) (childContracts signalType) :=
  ⟨.control, OneEntryFifo.Control.Rule.control⟩
private abbrev validOrRule (signalType : SignalType) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body signalType) (childContracts signalType) :=
  ⟨.outputValidOr, Primitives.OrRule.apply⟩
private abbrev dataMuxRule (signalType : SignalType) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body signalType) (childContracts signalType) :=
  ⟨.outputDataMux, Mux.Rule.select⟩

private def scheduleOrders (signalType : SignalType) :
    ScheduleDerivation.RuleScheduleOrders (body signalType)
      (childContracts signalType) (cycleContract signalType) where
  output
    | .forward => [validRule signalType, dataRule signalType,
        validOrRule signalType, dataMuxRule signalType]
    | .ready => [validRule signalType, controlOccurrence signalType]
  state := [validRule signalType, dataRule signalType,
    controlOccurrence signalType, validOrRule signalType, dataMuxRule signalType]

private def derivedRuleSchedules (signalType : SignalType) :
    ScheduleDerivation.DerivedRuleSchedules (body signalType)
      (childContracts signalType) (cycleContract signalType) := by
  derive_rule_schedules (scheduleOrders signalType)

private abbrev ruleSchedules (signalType : SignalType) :=
  (derivedRuleSchedules signalType).schedules

private theorem coversChildren (signalType : SignalType) :
    (ruleSchedules signalType).CoversChildren :=
  (derivedRuleSchedules signalType).coversChildren

section LayerCertification

variable (signalType : SignalType)
  (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
    (body signalType) (childContracts signalType))

private def stateCorresponds
    (contractState : (cycleContract signalType).state.Values)
    (structuralState : (Contracts.Cycle.Certification.Layer.moduleStructure
      (body signalType) layerChildren).State) : Prop :=
  (layerChildren .validStorage).certification.stateCorresponds
      (fun | .stored => contractState .storedValid)
      (structuralState .validStorage) ∧
    (layerChildren .dataStorage).certification.stateCorresponds
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

private theorem implements :
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body signalType) layerChildren)
      (cycleContract signalType)
      (stateCorresponds signalType layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  let validState : (EnabledResetRegister.cycleContract .bit false).state.Values :=
    fun | .stored => contractState .storedValid
  let dataState : (EnabledRegister.cycleContract signalType).state.Values :=
    fun | .stored => contractState .storedData
  have validCorresponds :
      (layerChildren .validStorage).certification.stateCorresponds
      validState
      (structuralState .validStorage) := corresponds.1
  have dataCorresponds :
      (layerChildren .dataStorage).certification.stateCorresponds
      dataState
      (structuralState .dataStorage) := corresponds.2
  have validMatches := Contracts.Cycle.Certification.Layer.childSolutionMatchesContract layerChildren
    inputs structuralState proposal satisfies .validStorage validState
      validCorresponds
  have dataMatches := Contracts.Cycle.Certification.Layer.childSolutionMatchesContract layerChildren
    inputs structuralState proposal satisfies .dataStorage dataState
      dataCorresponds
  have controlMatches :=
    letI : Subsingleton (childContracts signalType .control).state.Values := by
      change Subsingleton emptySignalMap.Values; infer_instance
    Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies .control SignalMap.emptyValues
  have validOrMatches :=
    letI : Subsingleton (childContracts signalType .outputValidOr).state.Values := by
      change Subsingleton emptySignalMap.Values; infer_instance
    Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies .outputValidOr SignalMap.emptyValues
  have muxMatches :=
    letI : Subsingleton (childContracts signalType .outputDataMux).state.Values := by
      change Subsingleton emptySignalMap.Values; infer_instance
    Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs structuralState proposal satisfies .outputDataMux SignalMap.emptyValues
  have boundary := satisfies.1
  rcases proposal with ⟨outputs, childValues⟩
  let validInputs := ProposedValues.childInputs (body signalType)
    (fun child => (layerChildren child).moduleStructure) inputs childValues
    Instance.validStorage
  let dataInputs := ProposedValues.childInputs (body signalType)
    (fun child => (layerChildren child).moduleStructure) inputs childValues
    Instance.dataStorage
  let controlInputs := ProposedValues.childInputs (body signalType)
    (fun child => (layerChildren child).moduleStructure) inputs childValues
    Instance.control
  let muxInputs := ProposedValues.childInputs (body signalType)
    (fun child => (layerChildren child).moduleStructure) inputs childValues
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
  change (layerChildren .validStorage).certification.stateCorresponds
    ((EnabledResetRegister.cycleContract .bit false).stateRule.apply validInputs validState)
    (childValues .validStorage).nextState at validNextCorresponds
  change (EnabledRegister.cycleContract signalType).EvaluatesTo dataInputs dataState
    (childValues .dataStorage).outputs
    ((EnabledRegister.cycleContract signalType).stateRule.apply dataInputs dataState)
      at dataEvaluates
  change (layerChildren .dataStorage).certification.stateCorresponds
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
    change (layerChildren .validStorage).certification.stateCorresponds
        nextValidState
        (childValues .validStorage).nextState ∧
      (layerChildren .dataStorage).certification.stateCorresponds
        nextDataState
        (childValues .dataStorage).nextState
    constructor
    · rw [validNextEq]
      exact validNextCorresponds
    · rw [dataNextEq]
      exact dataNextCorresponds

private theorem hasCorrespondingState
    (structuralState : (Contracts.Cycle.Certification.Layer.moduleStructure
      (body signalType) layerChildren).State) :
    ∃ contractState,
      stateCorresponds signalType layerChildren contractState structuralState := by
  rcases (layerChildren .validStorage).certification.hasCorrespondingState
      (structuralState .validStorage) with ⟨validState, validCorresponds⟩
  rcases (layerChildren .dataStorage).certification.hasCorrespondingState
      (structuralState .dataStorage) with ⟨dataState, dataCorresponds⟩
  exact ⟨(fun
    | .storedValid => validState .stored
    | .storedData => dataState .stored), ⟨validCorresponds, dataCorresponds⟩⟩

end LayerCertification

/-- The one-entry FIFO wiring implements its contract for any children
satisfying the five declared boundary contracts. -/
noncomputable opaque certifiedLayer (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleCertifiedLayer
      (body signalType) (childContracts signalType) (cycleContract signalType) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (ruleSchedules signalType) (coversChildren signalType)
    (stateCorresponds signalType) (hasCorrespondingState signalType)
    (implements signalType)

@[reducible] private noncomputable def certifiedChildren (signalType : SignalType) :
    Contracts.Cycle.Certification.Layer.ChildStructures
      (body signalType) (childContracts signalType)
  | .validStorage => (EnabledResetRegister.certified .bit false).certifiedStructure
  | .dataStorage => (EnabledRegister.certified signalType).certifiedStructure
  | .control => OneEntryFifo.Control.certified.certifiedStructure
  | .outputValidOr => Primitives.orCertified.certifiedStructure
  | .outputDataMux => Mux.certifiedStructure signalType

noncomputable opaque certification (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure signalType)
      (cycleContract signalType) :=
  (certifiedLayer signalType).certifyComposite
    (structuralChildren signalType) (certifiedChildren signalType) (by
      intro child
      cases child with
      | validStorage => exact EnabledResetRegister.certified_moduleStructure .bit false
      | dataStorage => rfl
      | control => rfl
      | outputValidOr => rfl
      | outputDataMux => exact Mux.certifiedStructure_moduleStructure signalType)

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
