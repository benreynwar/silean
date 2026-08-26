import Silean2.Modules.EnabledRegister
import Silean2.Modules.Mux
import Silean2.Modules.FifoControl
import Silean2.CertifiedSchedule

namespace Silean2.Modules.OneEntryFifo

open Silean2

inductive Input
  | inputValid
  | inputData
  | outputReady
deriving Enumeration

inductive Output
  | outputValid
  | outputData
  | inputReady
deriving Enumeration

@[reducible] def inputMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of Input fun
    | .inputValid | .outputReady => .bit
    | .inputData => signalType

@[reducible] def outputMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of Output fun
    | .outputValid | .inputReady => .bit
    | .outputData => signalType

@[reducible] def ports (signalType : SignalType) : ModulePorts :=
  ⟨inputMap signalType, outputMap signalType⟩

inductive Instance
  | validStorage
  | dataStorage
  | control
  | outputValidOr
  | outputDataMux
deriving Enumeration

@[reducible] def instances (signalType : SignalType) : Instances :=
  EnumeratedMap.of Instance fun
    | .validStorage => EnabledRegister.ports .bit
    | .dataStorage => EnabledRegister.ports signalType
    | .control => FifoControl.ports
    | .outputValidOr => Primitives.or.ports
    | .outputDataMux => Mux.ports signalType

@[reducible] def context (signalType : SignalType) : EndpointContext where
  ports := ports signalType
  instances := instances signalType

def wiring (signalType : SignalType) :
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

@[reducible] def body (signalType : SignalType) : ModuleBody :=
  ⟨context signalType, wiring signalType⟩

@[reducible] noncomputable def children (signalType : SignalType) :
    Certified.Children (body signalType)
  | .validStorage => EnabledRegister.certified .bit
  | .dataStorage => EnabledRegister.certified signalType
  | .control => FifoControl.certified
  | .outputValidOr => Primitives.orCertified
  | .outputDataMux => Mux.certified signalType

@[reducible] noncomputable def childStructure (signalType : SignalType) :=
  Certified.childStructure (children signalType)

noncomputable def moduleStructure (signalType : SignalType) :
    ModuleStructure (ports signalType) :=
  Certified.moduleStructure (body signalType) (children signalType)

inductive State
  | storedValid
  | storedData
deriving Enumeration

def stateMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of State fun
    | .storedValid => .bit
    | .storedData => signalType

inductive Rule
  | forward
  | ready
deriving Enumeration

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
  target := fun inputs state =>
    let update := (inputs .outputReady && state .storedValid) ||
      (!inputs .outputReady && !state .storedValid)
    fun
      | .storedValid => bif update then inputs .inputValid else state .storedValid
      | .storedData => bif update then inputs .inputData else state .storedData

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

abbrev validRule (signalType : SignalType) :
    Certified.RuleOccurrence (children signalType) :=
  ⟨.validStorage, EnabledRegister.Rule.observe⟩
abbrev dataRule (signalType : SignalType) :
    Certified.RuleOccurrence (children signalType) :=
  ⟨.dataStorage, EnabledRegister.Rule.observe⟩
abbrev controlOccurrence (signalType : SignalType) :
    Certified.RuleOccurrence (children signalType) :=
  ⟨.control, FifoControl.Rule.control⟩
abbrev validOrRule (signalType : SignalType) :
    Certified.RuleOccurrence (children signalType) :=
  ⟨.outputValidOr, Primitives.OrRule.apply⟩
abbrev dataMuxRule (signalType : SignalType) :
    Certified.RuleOccurrence (children signalType) :=
  ⟨.outputDataMux, Mux.Rule.select⟩

@[simp] theorem validRule_reads (signalType) : (validRule signalType).reads = [] := rfl
@[simp] theorem dataRule_reads (signalType) : (dataRule signalType).reads = [] := rfl
@[simp] theorem controlOccurrence_reads (signalType) :
    (controlOccurrence signalType).reads = [.storedValid, .downstreamReady] := rfl
@[simp] theorem validOrRule_reads (signalType) :
    (validOrRule signalType).reads = [.left, .right] := rfl
@[simp] theorem dataMuxRule_reads (signalType) :
    (dataMuxRule signalType).reads = [.select, .whenFalse, .whenTrue] := rfl
@[simp] theorem validRule_writes (signalType) :
    (validRule signalType).writes = [.value] := rfl
@[simp] theorem dataRule_writes (signalType) :
    (dataRule signalType).writes = [.value] := rfl
@[simp] theorem controlOccurrence_writes (signalType) :
    (controlOccurrence signalType).writes = [.upstreamReady, .storageUpdate] := rfl
@[simp] theorem validOrRule_writes (signalType) :
    (validOrRule signalType).writes = [.output] := rfl
@[simp] theorem dataMuxRule_writes (signalType) :
    (dataMuxRule signalType).writes = [.result] := rfl

def forwardSchedule (signalType : SignalType) :
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

def readySchedule (signalType : SignalType) :
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
        exact ⟨FifoControl.Rule.control, by simp, by simp⟩
    | outputValid | outputData =>
        simp [cycleContract, readyRule, SignalMap.select,
          SignalSelection.labels] at member)))

def stateSchedule (signalType : SignalType) :
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
  (.done trivial)))))

def ruleSchedules (signalType : SignalType) :
    Certified.RuleSchedules (body signalType) (children signalType)
      (cycleContract signalType) where
  output | .forward => forwardSchedule signalType | .ready => readySchedule signalType
  state := stateSchedule signalType

theorem coversChildren (signalType : SignalType) :
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
    change FifoControl.Rule at rule
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

theorem hasAtMostOneSolution (signalType : SignalType) :
    (moduleStructure signalType).HasAtMostOneSolution :=
  (ruleSchedules signalType).hasAtMostOneSolution (coversChildren signalType)

def controlInputsFrom (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values) (storedValid : Bool) :
    FifoControl.ports.inputs.Values
  | .storedValid => storedValid
  | .downstreamReady => inputs .outputReady

def validOrInputsFrom (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values) (storedValid : Bool) :
    Primitives.or.ports.inputs.Values
  | .left => storedValid
  | .right => inputs .inputValid

def dataMuxInputsFrom (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (storedValid : Bool) (storedData : signalType.Denote) :
    (Mux.ports signalType).inputs.Values
  | .select => storedValid
  | .whenFalse => inputs .inputData
  | .whenTrue => storedData

noncomputable def validStorageInputs (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (control : ProposedValues (children signalType .control).moduleStructure) :
    (EnabledRegister.ports .bit).inputs.Values
  | .value => inputs .inputValid
  | .enable => control.outputs .storageUpdate

noncomputable def dataStorageInputs (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (control : ProposedValues (children signalType .control).moduleStructure) :
    (EnabledRegister.ports signalType).inputs.Values
  | .value => inputs .inputData
  | .enable => control.outputs .storageUpdate

theorem hasStructuralResult (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (currentState : (moduleStructure signalType).State) :
    ∃ proposal, (moduleStructure signalType).IsSolution inputs currentState proposal := by
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

def stateCorresponds (signalType : SignalType)
    (contractState : (cycleContract signalType).state.Values)
    (structuralState : (moduleStructure signalType).State) : Prop :=
  EnabledRegister.stateCorresponds .bit
      (fun | .stored => contractState .storedValid)
      (structuralState .validStorage) ∧
    EnabledRegister.stateCorresponds signalType
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
    Implements (moduleStructure signalType) (cycleContract signalType)
      (stateCorresponds signalType) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, childValues⟩
  rcases satisfies with ⟨boundary, childSatisfies⟩
  let validInputs := ProposedValues.childInputs (body signalType) (childStructure signalType) inputs childValues
    Instance.validStorage
  let dataInputs := ProposedValues.childInputs (body signalType) (childStructure signalType) inputs childValues
    Instance.dataStorage
  let controlInputs := ProposedValues.childInputs (body signalType) (childStructure signalType) inputs childValues
    Instance.control
  let muxInputs := ProposedValues.childInputs (body signalType) (childStructure signalType) inputs childValues
    Instance.outputDataMux
  let validState : (EnabledRegister.cycleContract .bit).state.Values :=
    fun | .stored => contractState .storedValid
  let dataState : (EnabledRegister.cycleContract signalType).state.Values :=
    fun | .stored => contractState .storedData
  have validCorresponds : EnabledRegister.stateCorresponds .bit validState
      (structuralState .validStorage) := corresponds.1
  have dataCorresponds : EnabledRegister.stateCorresponds signalType dataState
      (structuralState .dataStorage) := corresponds.2
  rcases (EnabledRegister.certified .bit).implements validInputs validState
      (structuralState .validStorage) (childValues .validStorage)
      validCorresponds (childSatisfies .validStorage) with
    ⟨validNext, validEvaluates, validNextCorresponds⟩
  rcases (EnabledRegister.certified signalType).implements dataInputs dataState
      (structuralState .dataStorage) (childValues .dataStorage)
      dataCorresponds (childSatisfies .dataStorage) with
    ⟨dataNext, dataEvaluates, dataNextCorresponds⟩
  rcases FifoControl.certified.implements controlInputs SignalMap.emptyValues
      (structuralState .control) (childValues .control) (by trivial)
      (childSatisfies .control) with
    ⟨controlNext, controlEvaluates, controlNextCorresponds⟩
  rcases (Mux.certified signalType).implements muxInputs SignalMap.emptyValues
      (structuralState .outputDataMux) (childValues .outputDataMux) (by trivial)
      (childSatisfies .outputDataMux) with
    ⟨muxNext, muxEvaluates, muxNextCorresponds⟩
  refine ⟨(cycleContract signalType).stateRule.target inputs contractState, ?_, ?_⟩
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
        have outputOr := congrFun (childSatisfies .outputValidOr).1
          Primitives.SingleOutput.output
        change (childValues .outputValidOr).outputs .output = _ at outputOr
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
            SignalSource.value, Primitives.or] using outputOr
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
        have controlRule := controlEvaluates.1 FifoControl.Rule.control
        have validEquation := (EnabledRegister.outputRule_holds_iff .bit _ _ _).mp
          (validEvaluates.1 EnabledRegister.Rule.observe)
        simp [FifoControl.certified, FifoControl.cycleContract,
          FifoControl.controlRule,
          CycleOutputRule.Holds, SignalSelection.Matches,
          SignalSelection.project, SignalMap.select,
          SignalSelection.prepend] at controlRule
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
  · have validNextRule := validEvaluates.2
    have dataNextRule := dataEvaluates.2
    have controlRule := controlEvaluates.1 FifoControl.Rule.control
    have validOutputRule :=
      (EnabledRegister.outputRule_holds_iff .bit _ _ _).mp
        (validEvaluates.1 EnabledRegister.Rule.observe)
    simp [FifoControl.certified, FifoControl.cycleContract,
      FifoControl.controlRule,
      CycleOutputRule.Holds, SignalSelection.Matches,
      SignalSelection.project, SignalMap.select,
      SignalSelection.prepend] at controlRule
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
      rw [validNextRule]
      rfl
    have dataNextEquation : dataNext .stored =
        bif dataInputs .enable then dataInputs .value else dataState .stored := by
      rw [dataNextRule]
      rfl
    let nextValidState : (EnabledRegister.cycleContract .bit).state.Values :=
      fun | .stored => (cycleContract signalType).stateRule.target inputs contractState .storedValid
    let nextDataState : (EnabledRegister.cycleContract signalType).state.Values :=
      fun | .stored => (cycleContract signalType).stateRule.target inputs contractState .storedData
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
    change EnabledRegister.stateCorresponds .bit
        nextValidState
        (childValues .validStorage).nextState ∧
      EnabledRegister.stateCorresponds signalType
        nextDataState
        (childValues .dataStorage).nextState
    constructor
    · rw [validNextEq]
      exact validNextCorresponds
    · rw [dataNextEq]
      exact dataNextCorresponds

noncomputable def certified (signalType : SignalType) :
    ModuleCycleCertified (ports signalType) where
  moduleStructure := moduleStructure signalType
  cycleContract := cycleContract signalType
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

theorem hasExactlyOneSolution (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (currentState : (moduleStructure signalType).State) :
    ∃ proposal, (moduleStructure signalType).IsSolution inputs currentState proposal ∧
      ∀ other, (moduleStructure signalType).IsSolution inputs currentState other →
        other = proposal :=
  (certified signalType).hasExactlyOneStructuralResult inputs currentState

end Silean2.Modules.OneEntryFifo
