import Silean2.Modules.EnabledRegister
import Silean2.Modules.Mux
import Silean2.Modules.OneEntryFifoControl
import Silean2.Modules.NoResetFifoInterface
import Silean2.CertifiedSchedule
import Silean2.Naming.PrimitiveNaming

namespace Silean2.Modules.OneEntryFifo

open Silean2
open NoResetFifo

private inductive Instance
  | validStorage
  | dataStorage
  | control
  | outputValidOr
  | outputDataMux
deriving Enumeration

@[reducible] private def instances (signalType : SignalType) : Instances :=
  EnumeratedMap.of Instance fun
    | .validStorage => EnabledRegister.ports .bit
    | .dataStorage => EnabledRegister.ports signalType
    | .control => OneEntryFifoControl.ports
    | .outputValidOr => Primitives.or.ports
    | .outputDataMux => Mux.ports signalType

@[reducible] private def context (signalType : SignalType) : EndpointContext where
  ports := ports signalType
  instances := instances signalType

private def wiring (signalType : SignalType) :
    Wiring (context signalType).ports (context signalType).instances where
  moduleOutput
    | .outputValid => (context signalType).instanceOutput .outputValidOr .output
    | .outputData => (context signalType).instanceOutput .outputDataMux .result
    | .inputReady => (context signalType).instanceOutput .control .upstreamReady
  instanceInput
    | .validStorage, .enable => (context signalType).instanceOutput .control .storageUpdate
    | .validStorage, .value => (context signalType).moduleInput .inputValid
    | .dataStorage, .enable => (context signalType).instanceOutput .control .storageUpdate
    | .dataStorage, .value => (context signalType).moduleInput .inputData
    | .control, .storedValid => (context signalType).instanceOutput .validStorage .value
    | .control, .downstreamReady => (context signalType).moduleInput .outputReady
    | .outputValidOr, .left => (context signalType).instanceOutput .validStorage .value
    | .outputValidOr, .right => (context signalType).moduleInput .inputValid
    | .outputDataMux, .select => (context signalType).instanceOutput .validStorage .value
    | .outputDataMux, .whenFalse => (context signalType).moduleInput .inputData
    | .outputDataMux, .whenTrue => (context signalType).instanceOutput .dataStorage .value

@[reducible] private def body (signalType : SignalType) : ModuleBody :=
  ⟨context signalType, wiring signalType⟩

@[reducible] private noncomputable def children (signalType : SignalType) :
    Certified.Children (body signalType)
  | .validStorage => EnabledRegister.certified .bit
  | .dataStorage => EnabledRegister.certified signalType
  | .control => OneEntryFifoControl.certified
  | .outputValidOr => Primitives.orCertified
  | .outputDataMux => Mux.certified signalType

@[reducible] private noncomputable def childStructure (signalType : SignalType) :=
  Certified.childStructure (children signalType)

@[reducible] private def structuralChildren (signalType : SignalType) :
    (name : (instances signalType).Name) →
      ModuleStructure ((instances signalType).ports name)
  | .validStorage => EnabledRegister.moduleStructure .bit
  | .dataStorage => EnabledRegister.moduleStructure signalType
  | .control => OneEntryFifoControl.moduleStructure
  | .outputValidOr => Primitives.orCertified.moduleStructure
  | .outputDataMux => Mux.moduleStructure signalType

def moduleStructure (signalType : SignalType) :
    ModuleStructure (ports signalType) :=
  .composite (body signalType) (structuralChildren signalType)

private theorem moduleStructure_eq (signalType : SignalType) :
    moduleStructure signalType =
      Certified.moduleStructure (body signalType) (children signalType) := by
  unfold moduleStructure Certified.moduleStructure
  congr
  funext child
  cases child <;> rfl

inductive State
  | storedValid
  | storedData
deriving Enumeration

def stateMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of State fun
    | .storedValid => .bit
    | .storedData => signalType

def forwardRule (signalType : SignalType) :
    CycleOutputRule (ports signalType) (stateMap signalType)
      (.ofLists [.bit, signalType] [.bit, signalType]) where
  readsInputs := ((inputMap signalType).select .inputData).prepend .inputValid
  writesOutputs := ((outputMap signalType).select .outputData).prepend .outputValid
  target
    | (inputValid, (inputData, ())), state =>
        (state .storedValid || inputValid,
          (bif state .storedValid then state .storedData else inputData, ()))

def readyRule (signalType : SignalType) :
    CycleOutputRule (ports signalType) (stateMap signalType)
    (.ofLists [.bit] [.bit]) where
  readsInputs := (inputMap signalType).select .outputReady
  writesOutputs := (outputMap signalType).select .inputReady
  target
    | (outputReady, ()), state =>
        (outputReady || !state .storedValid, ())

def stateRule (signalType : SignalType) :
    CycleStateRule (ports signalType) (stateMap signalType) where
  inputTypes := .cons .bit (.cons .bit (.cons signalType .nil))
  readsInputs := (((inputMap signalType).select .inputData).prepend .inputValid).prepend
    .outputReady
  target
    | (outputReady, (inputValid, (inputData, ()))), state =>
        let update := (outputReady && state .storedValid) ||
          (!outputReady && !state .storedValid)
        fun
          | .storedValid => bif update then inputValid else state .storedValid
          | .storedData => bif update then inputData else state .storedData

def cycleContract (signalType : SignalType) :
    ModuleCycleContract (ports signalType) where
  state := stateMap signalType
  RuleName := Rule
  ruleNames := inferInstance
  outputRule
    | .forward => ⟨_, forwardRule signalType⟩
    | .ready => ⟨_, readyRule signalType⟩
  stateRule := stateRule signalType
  outputCoverage := by rfl

private abbrev validRule (signalType : SignalType) :
    Certified.RuleOccurrence (children signalType) :=
  ⟨.validStorage, EnabledRegister.Rule.observe⟩
private abbrev dataRule (signalType : SignalType) :
    Certified.RuleOccurrence (children signalType) :=
  ⟨.dataStorage, EnabledRegister.Rule.observe⟩
private abbrev controlOccurrence (signalType : SignalType) :
    Certified.RuleOccurrence (children signalType) :=
  ⟨.control, OneEntryFifoControl.Rule.control⟩
private abbrev validOrRule (signalType : SignalType) :
    Certified.RuleOccurrence (children signalType) :=
  ⟨.outputValidOr, Primitives.OrRule.apply⟩
private abbrev dataMuxRule (signalType : SignalType) :
    Certified.RuleOccurrence (children signalType) :=
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
    Certified.OutputSchedule (body signalType) (children signalType)
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
        | left => exact ⟨EnabledRegister.Rule.observe, by simp, by simp⟩
        | right => simp [cycleContract, forwardRule, SignalSelection.prepend,
            SignalMap.select, SignalSelection.labels, Certified.sourceAvailable,
            body, wiring, context, EndpointContext.moduleInput])
    (by simp)
  (.call (dataMuxRule signalType)
    (by intro input member
        cases input with
        | select => exact ⟨EnabledRegister.Rule.observe, by simp, by simp⟩
        | whenFalse => simp [cycleContract, forwardRule,
            SignalSelection.prepend, SignalMap.select, SignalSelection.labels,
            Certified.sourceAvailable, body, wiring, context,
            EndpointContext.moduleInput]
        | whenTrue => exact ⟨EnabledRegister.Rule.observe, by simp, by simp⟩)
    (by simp)
  (.done (by
    intro output member
    cases output with
    | outputValid =>
        change Certified.outputAvailable
          ([dataMuxRule signalType, validOrRule signalType, dataRule signalType, validRule signalType] :
            Certified.Availability (children signalType)) Instance.outputValidOr .output
        exact ⟨Primitives.OrRule.apply, by simp, by simp⟩
    | outputData =>
        change Certified.outputAvailable
          ([dataMuxRule signalType, validOrRule signalType, dataRule signalType, validRule signalType] :
            Certified.Availability (children signalType)) Instance.outputDataMux .result
        exact ⟨Mux.Rule.select, by simp, by simp⟩
    | inputReady =>
        simp [cycleContract, forwardRule, SignalSelection.prepend,
          SignalMap.select, SignalSelection.labels] at member)))))

private def readySchedule (signalType : SignalType) :
    Certified.OutputSchedule (body signalType) (children signalType)
      (cycleContract signalType) .ready :=
  .call (validRule signalType)
    (by intro input member; cases member)
    (by simp)
  (.call (controlOccurrence signalType)
    (by intro input member
        cases input with
        | storedValid => exact ⟨EnabledRegister.Rule.observe, by simp, by simp⟩
        | downstreamReady => simp [cycleContract, readyRule, SignalMap.select,
            SignalSelection.labels, Certified.sourceAvailable, body, wiring,
            context, EndpointContext.moduleInput])
    (by simp)
  (.done (by
    intro output member
    cases output with
    | inputReady =>
        change Certified.outputAvailable
          ([controlOccurrence signalType, validRule signalType] :
            Certified.Availability (children signalType))
          Instance.control .upstreamReady
        exact ⟨OneEntryFifoControl.Rule.control, by simp, by simp⟩
    | outputValid | outputData =>
        simp [cycleContract, readyRule, SignalMap.select,
          SignalSelection.labels] at member)))

private def stateSchedule (signalType : SignalType) :
    Certified.StateSchedule (body signalType) (children signalType) :=
  .call (validRule signalType) (by intro input member; cases member) (by simp)
  (.call (dataRule signalType) (by intro input member; cases member) (by simp)
  (.call (controlOccurrence signalType)
    (by intro input member
        cases input with
        | storedValid => exact ⟨EnabledRegister.Rule.observe, by simp, by simp⟩
        | downstreamReady => trivial)
    (by simp)
  (.call (validOrRule signalType)
    (by intro input member
        cases input with
        | left => exact ⟨EnabledRegister.Rule.observe, by simp, by simp⟩
        | right => trivial)
    (by simp)
  (.call (dataMuxRule signalType)
    (by intro input member
        cases input with
        | select => exact ⟨EnabledRegister.Rule.observe, by simp, by simp⟩
        | whenFalse => trivial
        | whenTrue => exact ⟨EnabledRegister.Rule.observe, by simp, by simp⟩)
    (by simp)
  (.done (by
    intro child input member
    cases child with
    | validStorage | dataStorage =>
        rw [EnabledRegister.certified_cycleContract] at member
        cases input with
        | enable => exact ⟨OneEntryFifoControl.Rule.control, by simp, by simp⟩
        | value => trivial
    | control =>
        rw [OneEntryFifoControl.certified_cycleContract] at member
        simp [OneEntryFifoControl.cycleContract, CycleStateRule.empty,
          SignalSelection.labels] at member
    | outputValidOr =>
        simp [children, Primitives.orCertified, Primitives.orCycleContract,
          CycleStateRule.empty, SignalSelection.labels] at member
    | outputDataMux =>
        rw [Mux.certified_cycleContract] at member
        simp [Mux.cycleContract, Mux.stateRule, CycleStateRule.empty,
          SignalSelection.labels] at member))))))

private def ruleSchedules (signalType : SignalType) :
    Certified.RuleSchedules (body signalType) (children signalType)
      (cycleContract signalType) where
  output | .forward => forwardSchedule signalType | .ready => readySchedule signalType
  state := stateSchedule signalType

private theorem coversChildren (signalType : SignalType) :
    (ruleSchedules signalType).CoversChildren := by
  intro child rule
  cases child with
  | validStorage =>
    change EnabledRegister.Rule at rule
    cases rule
    apply Certified.RuleSchedules.Combined.add_includes
    change validRule signalType ∈ (stateSchedule signalType).finalAvailability
    simp [stateSchedule, Certified.Schedule.finalAvailability]
  | dataStorage =>
    change EnabledRegister.Rule at rule
    cases rule
    apply Certified.RuleSchedules.Combined.add_includes
    change dataRule signalType ∈ (stateSchedule signalType).finalAvailability
    simp [stateSchedule, Certified.Schedule.finalAvailability]
  | control =>
    change OneEntryFifoControl.Rule at rule
    cases rule
    apply Certified.RuleSchedules.Combined.add_includes
    change controlOccurrence signalType ∈ (stateSchedule signalType).finalAvailability
    simp [stateSchedule, Certified.Schedule.finalAvailability]
  | outputValidOr =>
    change Primitives.OrRule at rule
    cases rule
    apply Certified.RuleSchedules.Combined.add_includes
    change validOrRule signalType ∈ (stateSchedule signalType).finalAvailability
    simp [stateSchedule, Certified.Schedule.finalAvailability]
  | outputDataMux =>
    change Mux.Rule at rule
    cases rule
    apply Certified.RuleSchedules.Combined.add_includes
    change dataMuxRule signalType ∈ (stateSchedule signalType).finalAvailability
    simp [stateSchedule, Certified.Schedule.finalAvailability]

private theorem hasAtMostOneSolution (signalType : SignalType) :
    (Certified.moduleStructure (body signalType)
      (children signalType)).HasAtMostOneSolution :=
  (ruleSchedules signalType).hasAtMostOneSolution (coversChildren signalType)

private def controlInputsFrom (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values) (storedValid : Bool) :
    OneEntryFifoControl.ports.inputs.Values
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
    (EnabledRegister.ports .bit).inputs.Values
  | .value => inputs .inputValid
  | .enable => control.outputs .storageUpdate

private noncomputable def dataStorageInputs (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (control : ProposedValues (children signalType .control).moduleStructure) :
    (EnabledRegister.ports signalType).inputs.Values
  | .value => inputs .inputData
  | .enable => control.outputs .storageUpdate

private theorem hasStructuralResult (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (currentState : (Certified.moduleStructure (body signalType)
      (children signalType)).State) :
    ∃ proposal, (Certified.moduleStructure (body signalType)
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
    (EnabledRegister.outputRule_holds_iff .bit _ _ _).mp
      (validEvaluates.1 EnabledRegister.Rule.observe)
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
    (structuralState : (Certified.moduleStructure (body signalType)
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
  simp [CycleOutputRule.Holds, forwardRule, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select, SignalSelection.prepend]
  intro
  rfl

theorem readyRule_holds_iff (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : (cycleContract signalType).state.Values)
    (outputs : (ports signalType).outputs.Values) :
    (readyRule signalType).Holds inputs state outputs ↔
      outputs .inputReady = (inputs .outputReady || !state .storedValid) := by
  simp [CycleOutputRule.Holds, readyRule, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select]

private theorem implements (signalType : SignalType) :
    Implements (Certified.moduleStructure (body signalType)
      (children signalType)) (cycleContract signalType)
      (stateCorresponds signalType) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  let validState : (EnabledRegister.cycleContract .bit).state.Values :=
    fun | .stored => contractState .storedValid
  let dataState : (EnabledRegister.cycleContract signalType).state.Values :=
    fun | .stored => contractState .storedData
  have validCorresponds : (children signalType .validStorage).stateCorresponds
      validState
      (structuralState .validStorage) := corresponds.1
  have dataCorresponds : (children signalType .dataStorage).stateCorresponds
      dataState
      (structuralState .dataStorage) := corresponds.2
  have validMatches := Certified.childSolutionMatchesContract (children signalType)
    inputs structuralState proposal satisfies .validStorage validState
      validCorresponds
  have dataMatches := Certified.childSolutionMatchesContract (children signalType)
    inputs structuralState proposal satisfies .dataStorage dataState
      dataCorresponds
  rcases (children signalType .control).hasCorrespondingState
      (structuralState .control) with ⟨controlState, controlCorresponds⟩
  have controlState_eq : controlState = SignalMap.emptyValues := by
    funext statePort
    exact nomatch statePort
  subst controlState
  have controlMatches := Certified.childSolutionMatchesContract (children signalType)
    inputs structuralState proposal satisfies .control SignalMap.emptyValues
      controlCorresponds
  have validOrMatches := Certified.childSolutionMatchesContract (children signalType)
    inputs structuralState proposal satisfies .outputValidOr SignalMap.emptyValues
      (by trivial)
  rcases (children signalType .outputDataMux).hasCorrespondingState
      (structuralState .outputDataMux) with ⟨muxState, muxCorresponds⟩
  have muxState_eq : muxState = SignalMap.emptyValues := by
    funext statePort
    exact nomatch statePort
  subst muxState
  have muxMatches := Certified.childSolutionMatchesContract (children signalType)
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
  change (EnabledRegister.cycleContract .bit).EvaluatesTo validInputs validState
    (childValues .validStorage).outputs
    ((EnabledRegister.cycleContract .bit).stateRule.apply validInputs validState)
      at validEvaluates
  change (children signalType .validStorage).stateCorresponds
    ((EnabledRegister.cycleContract .bit).stateRule.apply validInputs validState)
    (childValues .validStorage).nextState at validNextCorresponds
  change (EnabledRegister.cycleContract signalType).EvaluatesTo dataInputs dataState
    (childValues .dataStorage).outputs
    ((EnabledRegister.cycleContract signalType).stateRule.apply dataInputs dataState)
      at dataEvaluates
  change (children signalType .dataStorage).stateCorresponds
    ((EnabledRegister.cycleContract signalType).stateRule.apply dataInputs dataState)
    (childValues .dataStorage).nextState at dataNextCorresponds
  let validNext := (EnabledRegister.cycleContract .bit).stateRule.apply
    validInputs validState
  let dataNext := (EnabledRegister.cycleContract signalType).stateRule.apply
    dataInputs dataState
  refine ⟨(cycleContract signalType).stateRule.apply inputs contractState, ?_, ?_⟩
  · constructor
    · intro name
      cases name
      · change (forwardRule signalType).Holds inputs contractState _
        rw [forwardRule_holds_iff signalType]
        have validEquation := (EnabledRegister.outputRule_holds_iff .bit _ _ _).mp
          (validEvaluates.1 EnabledRegister.Rule.observe)
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
              boundary Output.outputValid
        have dataBoundary : outputs .outputData =
            (childValues .outputDataMux).outputs .result := by
          simpa [ProposedValues.boundaryOutputsSatisfy, body, wiring, context,
            EndpointContext.instanceOutput, SignalSource.value] using
              boundary Output.outputData
        have orEquation : (childValues .outputValidOr).outputs .output =
            ((childValues .validStorage).outputs .value || inputs .inputValid) := by
          simpa [ProposedValues.childInputs, body, wiring, context, instances,
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
        have controlRule := (OneEntryFifoControl.controlRule_holds_iff _ _ _).mp
          (controlEvaluates.1 OneEntryFifoControl.Rule.control)
        have validEquation := (EnabledRegister.outputRule_holds_iff .bit _ _ _).mp
          (validEvaluates.1 EnabledRegister.Rule.observe)
        change (childValues .validStorage).outputs .value =
          contractState .storedValid at validEquation
        change (childValues .control).outputs .upstreamReady =
            (controlInputs .downstreamReady || !controlInputs .storedValid) ∧
          _ at controlRule
        have readyBoundary : outputs .inputReady =
            (childValues .control).outputs .upstreamReady := by
          simpa [ProposedValues.boundaryOutputsSatisfy, body, wiring, context,
            EndpointContext.instanceOutput, SignalSource.value] using
              boundary Output.inputReady
        have readyEquation : (childValues .control).outputs .upstreamReady =
            (inputs .outputReady || !(childValues .validStorage).outputs .value) := by
          have downstream : controlInputs .downstreamReady = inputs .outputReady := by
            simp [controlInputs, ProposedValues.childInputs, body, wiring,
              context, instances, EndpointContext.moduleInput,
              EndpointContext.instanceOutput, SignalSource.value]
          have stored : controlInputs .storedValid =
              (childValues .validStorage).outputs .value := by
            simp [controlInputs, ProposedValues.childInputs, body, wiring,
              context, instances, EndpointContext.moduleInput,
              EndpointContext.instanceOutput, SignalSource.value]
          rw [downstream, stored] at controlRule
          exact controlRule.1
        rw [validEquation] at readyEquation
        exact readyBoundary.trans readyEquation
    · rfl
  · have controlRule := (OneEntryFifoControl.controlRule_holds_iff _ _ _).mp
      (controlEvaluates.1 OneEntryFifoControl.Rule.control)
    have validOutputRule :=
      (EnabledRegister.outputRule_holds_iff .bit _ _ _).mp
        (validEvaluates.1 EnabledRegister.Rule.observe)
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
        bif validInputs .enable then validInputs .value else validState .stored := by
      rfl
    have dataNextEquation : dataNext .stored =
        bif dataInputs .enable then dataInputs .value else dataState .stored := by
      rfl
    let nextValidState : (EnabledRegister.cycleContract .bit).state.Values :=
      fun | .stored => (cycleContract signalType).stateRule.apply inputs contractState .storedValid
    let nextDataState : (EnabledRegister.cycleContract signalType).state.Values :=
      fun | .stored => (cycleContract signalType).stateRule.apply inputs contractState .storedData
    have validNextEq : nextValidState = validNext := by
      funext statePort
      cases statePort
      rw [validNextEquation]
      simp [validInputs, ProposedValues.childInputs, body, wiring, context,
        instances, EndpointContext.moduleInput, EndpointContext.instanceOutput,
        SignalSource.value, validState]
      exact congrArg
        (fun update => bif update then inputs .inputValid
          else contractState .storedValid) updateEquation.symm
    have dataNextEq : nextDataState = dataNext := by
      funext statePort
      cases statePort
      rw [dataNextEquation]
      simp [dataInputs, ProposedValues.childInputs, body, wiring, context,
        instances, EndpointContext.moduleInput, EndpointContext.instanceOutput,
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
    ModuleCycleCertification
      (Certified.moduleStructure (body signalType) (children signalType))
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
    ModuleCycleCertification (moduleStructure signalType)
      (cycleContract signalType) :=
  (proofCertification signalType).transportStructure
    (moduleStructure_eq signalType).symm

noncomputable def certified (signalType : SignalType) :
    ModuleCycleCertified (ports signalType) :=
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

end Silean2.Modules.OneEntryFifo

namespace Silean2.Modules.OneEntryFifo.Naming

open Silean2 Silean2.Naming

def portsWithNaming (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) :
    ModulePortsNaming (Modules.NoResetFifo.ports signalType) where
  inputs := ⟨fun
    | .inputValid => "input_valid"
    | .inputData => "input_data"
    | .outputReady => "output_ready"⟩
  outputs := ⟨fun
    | .outputValid => "output_valid"
    | .outputData => "output_data"
    | .inputReady => "input_ready"⟩
  inputTypes := fun
    | .inputValid | .outputReady => .bit
    | .inputData => typeNaming
  outputTypes := fun
    | .outputValid | .inputReady => .bit
    | .outputData => typeNaming

def ports (signalType : SignalType) :
    ModulePortsNaming (Modules.NoResetFifo.ports signalType) :=
  portsWithNaming signalType (.positional signalType)

def namingWith (signalType : SignalType) (typeNaming : SignalTypeNaming signalType) :
    ModuleNaming (Modules.OneEntryFifo.moduleStructure signalType) := by
  unfold Modules.OneEntryFifo.moduleStructure
  exact .composite ⟨"one_entry_fifo", "structural", [.shape signalType]⟩
    (portsWithNaming signalType typeNaming)
    (fun
      | .validStorage => "valid_storage"
      | .dataStorage => "data_storage"
      | .control => "control"
      | .outputValidOr => "output_valid_or"
      | .outputDataMux => "output_data_mux")
    (fun
      | .validStorage => Modules.EnabledRegister.Naming.naming .bit
      | .dataStorage => Modules.EnabledRegister.Naming.namingWith signalType typeNaming
      | .control => Modules.OneEntryFifoControl.Naming.naming
      | .outputValidOr => Silean2.Naming.Primitive.or
      | .outputDataMux => Modules.Mux.Naming.namingWith signalType typeNaming)

def naming (signalType : SignalType) :
    ModuleNaming (Modules.OneEntryFifo.moduleStructure signalType) :=
  namingWith signalType (.positional signalType)

end Silean2.Modules.OneEntryFifo.Naming
