import Silean2.CertifiedSchedule
import Silean2.Modules.Mux
import Silean2.Modules.Register

namespace Silean2.Modules.EnabledRegister

open Silean2

inductive Instance
  | selection
  | storage
deriving Enumeration

@[reducible] def instances (signalType : SignalType) : Instances :=
  EnumeratedMap.of Instance fun
    | .selection => Modules.Mux.ports signalType
    | .storage => Modules.Register.ports signalType

inductive Input
  | value
  | enable
deriving Enumeration

inductive Output
  | value
deriving Enumeration

@[reducible] def inputMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of Input fun
    | .value => signalType
    | .enable => .bit

@[reducible] def outputMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of Output fun | .value => signalType

@[reducible] def ports (signalType : SignalType) : ModulePorts :=
  ⟨inputMap signalType, outputMap signalType⟩

@[reducible] def context (signalType : SignalType) : EndpointContext where
  ports := ports signalType
  instances := instances signalType

def wiring (signalType : SignalType) :
    Wiring (context signalType).ports (context signalType).instances where
  moduleOutput
    | .value => (context signalType).instanceOutput .storage .output
  instanceInput
    | .selection, .select => (context signalType).moduleInput .enable
    | .selection, .whenFalse =>
        (context signalType).instanceOutput .storage .output
    | .selection, .whenTrue => (context signalType).moduleInput .value
    | .storage, .input => (context signalType).instanceOutput .selection .result

@[reducible] def body (signalType : SignalType) : ModuleBody :=
  ⟨context signalType, wiring signalType⟩

@[reducible] noncomputable def children (signalType : SignalType) :
    Certified.Children (body signalType)
  | .selection => Modules.Mux.certified signalType
  | .storage => Modules.Register.certified signalType

@[reducible] noncomputable def childStructure (signalType : SignalType) :=
  Certified.childStructure (children signalType)

noncomputable def moduleStructure (signalType : SignalType) :
    ModuleStructure (ports signalType) :=
  Certified.moduleStructure (body signalType) (children signalType)

end Silean2.Modules.EnabledRegister

namespace Silean2.Modules.EnabledRegister
open Silean2
inductive Rule | observe
deriving Enumeration
def outputRule (signalType : SignalType) :
    CycleOutputRule (Modules.EnabledRegister.ports signalType)
      (Modules.Register.stateMap signalType)
      { inputTypes := .nil, outputTypes := .cons signalType .nil } where
  readsInputs := .nil
  writesOutputs := (Modules.EnabledRegister.ports signalType).outputs.select .value
  target | (), state => (state .stored, ())
def stateRule (signalType : SignalType) :
    CycleStateRule (Modules.EnabledRegister.ports signalType)
      (Modules.Register.stateMap signalType) where
  target := fun inputs state => fun
    | .stored => bif inputs .enable then inputs .value else state .stored
def cycleContract (signalType : SignalType) :
    ModuleCycleContract (Modules.EnabledRegister.ports signalType) where
  state := Modules.Register.stateMap signalType
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .observe => ⟨_, outputRule signalType⟩
  stateRule := stateRule signalType
  outputCoverage := by rfl

abbrev selectionRule (signalType : SignalType) :
    Certified.RuleOccurrence (children signalType) :=
  ⟨.selection, Mux.Rule.select⟩

abbrev storageRule (signalType : SignalType) :
    Certified.RuleOccurrence (children signalType) :=
  ⟨.storage, Primitives.RegisterRule.observe⟩

@[simp] theorem selectionRule_reads (signalType) :
    (selectionRule signalType).reads = [.select, .whenFalse, .whenTrue] := rfl
@[simp] theorem selectionRule_writes (signalType) :
    (selectionRule signalType).writes = [.result] := rfl
@[simp] theorem storageRule_reads (signalType) :
    (storageRule signalType).reads = [] := rfl
@[simp] theorem storageRule_writes (signalType) :
    (storageRule signalType).writes = [.output] := rfl

def outputSchedule (signalType : SignalType) :
    Certified.OutputSchedule (body signalType) (children signalType)
      (cycleContract signalType) .observe :=
  .call (storageRule signalType)
    (by intro port member; cases port; cases member)
    (by simp)
  (.done (by
    intro output member
    cases output
    change Certified.outputAvailable ([storageRule signalType] :
      Certified.Availability (children signalType)) .storage .output
    exact ⟨Primitives.RegisterRule.observe, by simp, by simp⟩))

def stateSchedule (signalType : SignalType) :
    Certified.StateSchedule (body signalType) (children signalType) :=
  .call (storageRule signalType)
    (by intro port member; cases port; cases member)
    (by simp)
  (.call (selectionRule signalType)
    (by intro input member
        cases input with
        | select => trivial
        | whenFalse =>
            exact ⟨Primitives.RegisterRule.observe, by simp, by simp⟩
        | whenTrue => trivial)
    (by simp)
  (.done trivial))

def ruleSchedules (signalType : SignalType) :
    Certified.RuleSchedules (body signalType) (children signalType)
      (cycleContract signalType) where
  output | .observe => outputSchedule signalType
  state := stateSchedule signalType

theorem coversChildren (signalType : SignalType) :
    (ruleSchedules signalType).CoversChildren := by
  intro child rule
  cases child with
  | selection =>
    change Mux.Rule at rule
    cases rule
    apply Certified.RuleSchedules.Combined.add_includes
    change selectionRule signalType ∈ (stateSchedule signalType).finalAvailability
    simp [stateSchedule, Certified.Schedule.finalAvailability]
  | storage =>
    change Register.Rule at rule
    cases rule
    apply Certified.RuleSchedules.Combined.add_preserves
    apply Certified.RuleSchedules.mem_combineOutputs (ruleSchedules signalType) .observe
    change storageRule signalType ∈ (outputSchedule signalType).finalAvailability
    simp [outputSchedule, Certified.Schedule.finalAvailability]

theorem hasAtMostOneSolution (signalType : SignalType) :
    (moduleStructure signalType).HasAtMostOneSolution :=
  (ruleSchedules signalType).hasAtMostOneSolution (coversChildren signalType)

def selectionInputs (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values) (stored : signalType.Denote) :
    (Mux.ports signalType).inputs.Values
  | .select => inputs .enable
  | .whenFalse => stored
  | .whenTrue => inputs .value

noncomputable def storageInputs (signalType : SignalType)
    (selection : ProposedValues
      (children signalType .selection).moduleStructure) :
    (Register.ports signalType).inputs.Values
  | .input => selection.outputs .result

theorem hasStructuralResult (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (currentState : (moduleStructure signalType).State) :
    ∃ proposal,
      (moduleStructure signalType).IsSolution inputs currentState proposal := by
  rcases (children signalType .storage).hasCorrespondingState
      (currentState .storage) with ⟨storageState, storageCorresponds⟩
  rcases (children signalType .selection).hasStructuralResult
      (selectionInputs signalType inputs (storageState .stored))
      (currentState .selection) with ⟨selection, selectionSatisfies⟩
  rcases (children signalType .storage).hasStructuralResult
      (storageInputs signalType selection)
      (currentState .storage) with ⟨storage, storageSatisfies⟩
  have storageOutput : storage.outputs .output =
      storageState .stored := by
    rcases (children signalType .storage).implements
        (storageInputs signalType selection) storageState
        (currentState .storage) storage storageCorresponds storageSatisfies with
      ⟨nextState, evaluates, nextCorresponds⟩
    exact (Register.outputRule_holds_iff signalType _ _ _).mp
      (evaluates.1 Primitives.RegisterRule.observe)
  let childProposals : (name : Instance) →
      ProposedValues (childStructure signalType name)
    | .selection => selection
    | .storage => storage
  let outputs : (ports signalType).outputs.Values := fun
    | .value => storage.outputs .output
  refine ⟨ProposedValues.composite outputs childProposals, ?_⟩
  constructor
  · intro output
    cases output
    rfl
  · intro child
    cases child with
    | selection =>
        change (children signalType .selection).moduleStructure.IsSolution
          (ProposedValues.childInputs (body signalType)
            (childStructure signalType) inputs childProposals
            .selection) (currentState .selection) selection
        rw [show ProposedValues.childInputs (body signalType)
          (childStructure signalType) inputs
          childProposals .selection =
            selectionInputs signalType inputs (storageState .stored) by
          funext port
          cases port with
          | select => rfl
          | whenFalse => exact storageOutput
          | whenTrue => rfl]
        exact selectionSatisfies
    | storage =>
        change (children signalType .storage).moduleStructure.IsSolution
          (ProposedValues.childInputs (body signalType)
            (childStructure signalType) inputs childProposals
            .storage) (currentState .storage) storage
        rw [show ProposedValues.childInputs (body signalType)
          (childStructure signalType) inputs childProposals .storage =
            storageInputs signalType selection by
            funext port; cases port; rfl]
        exact storageSatisfies

def stateCorresponds (signalType : SignalType)
    (contractState : (cycleContract signalType).state.Values)
    (structuralState : (moduleStructure signalType).State) : Prop :=
  (children signalType .storage).stateCorresponds contractState
    (structuralState .storage)

@[simp] theorem outputRule_holds_iff (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : (cycleContract signalType).state.Values)
    (outputs : (ports signalType).outputs.Values) :
    (outputRule signalType).Holds inputs state outputs ↔
      outputs .value = state .stored := by
  simp [CycleOutputRule.Holds, outputRule, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select]

private theorem implements (signalType : SignalType) :
    Implements (moduleStructure signalType) (cycleContract signalType)
      (stateCorresponds signalType) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, childProposals⟩
  rcases satisfies with ⟨boundary, childSatisfies⟩
  rcases (children signalType .storage).implements
      (ProposedValues.childInputs (body signalType) (childStructure signalType)
        inputs childProposals .storage)
      contractState (structuralState .storage) (childProposals .storage)
      corresponds (childSatisfies .storage) with
    ⟨storageNextState, storageEvaluates, storageNextCorresponds⟩
  rcases (children signalType .selection).implements
      (ProposedValues.childInputs (body signalType) (childStructure signalType)
        inputs childProposals .selection)
      SignalMap.emptyValues (structuralState .selection)
      (childProposals .selection) trivial (childSatisfies .selection) with
    ⟨selectionNextState, selectionEvaluates, selectionNextCorresponds⟩
  refine ⟨storageNextState, ?_, storageNextCorresponds⟩
  constructor
  · intro name
    cases name
    change (outputRule signalType).Holds inputs contractState _
    rw [outputRule_holds_iff signalType]
    have boundaryOutput := boundary .value
    change outputs .value = (childProposals .storage).outputs .output at boundaryOutput
    exact boundaryOutput.trans ((Register.outputRule_holds_iff signalType _ _ _).mp
      (storageEvaluates.1 Primitives.RegisterRule.observe))
  · have storageNextValue : storageNextState .stored =
        (ProposedValues.childInputs (body signalType) (childStructure signalType)
          inputs childProposals .storage) .input := by
      simpa [children, Register.certified, Register.Implementation.certified,
        Register.cycleContract, Register.stateRule] using
        congrFun storageEvaluates.2 Primitives.RegisterState.stored
    have selected := selectionEvaluates.1 Mux.Rule.select
    change (Mux.selectRule signalType).Holds _ SignalMap.emptyValues _ at selected
    simp [CycleOutputRule.Holds, Mux.selectRule, SignalSelection.Matches,
      SignalSelection.project, SignalMap.select, SignalSelection.prepend] at selected
    change (childProposals .selection).outputs .result =
      bif inputs .enable then inputs .value
        else (childProposals .storage).outputs .output at selected
    have storageCurrent := (Register.outputRule_holds_iff signalType _ _ _).mp
      (storageEvaluates.1 Primitives.RegisterRule.observe)
    funext statePort
    cases statePort
    rw [storageNextValue]
    change (childProposals .selection).outputs .result =
      bif inputs .enable then inputs .value else contractState .stored
    rw [selected, storageCurrent]

noncomputable def certified (signalType : SignalType) :
    ModuleCycleCertified (ports signalType) where
  moduleStructure := moduleStructure signalType
  cycleContract := cycleContract signalType
  stateCorresponds := stateCorresponds signalType
  hasCorrespondingState := fun structuralState =>
    (children signalType .storage).hasCorrespondingState
      (structuralState .storage)
  hasStructuralResult := hasStructuralResult signalType
  structuralResultUnique := hasAtMostOneSolution signalType
  implements := implements signalType

theorem hasExactlyOneSolution (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (currentState : (moduleStructure signalType).State) :
    ∃ proposal,
      (moduleStructure signalType).IsSolution inputs currentState proposal ∧
      ∀ other, (moduleStructure signalType).IsSolution inputs currentState other →
        other = proposal :=
  (certified signalType).hasExactlyOneStructuralResult inputs currentState
end Silean2.Modules.EnabledRegister
