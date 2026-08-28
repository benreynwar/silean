import Silean.Contracts.Cycle.CycleSchedule
import Silean.Modules.Mux
import Silean.Modules.Register

namespace Silean.Modules.EnabledRegister

open Silean

/-! ## Hardware structure -/

/-- A register which loads `value` when `enable` is high and otherwise retains
its current value. -/
inductive Instance
  /-- Chooses between the new input and the stored value. -/
  | selection
  /-- Holds the selected value across cycles. -/
  | storage
deriving Enumeration

@[reducible] def instancePorts (signalType : SignalType) : InstancePorts :=
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
  instancePorts := instancePorts signalType

def wiring (signalType : SignalType) :
    Wiring (context signalType).ports (context signalType).instancePorts :=
  let c := context signalType
  { moduleOutput := fun
    -- The stored value is exposed directly.
    | .value => c.instanceOutput .storage .output
    instanceInput := fun
    -- Select the new input when enabled, or feed the stored value back.
    | .selection, .select => c.moduleInput .enable
    | .selection, .whenFalse =>
        c.instanceOutput .storage .output
    | .selection, .whenTrue => c.moduleInput .value
    -- Store the mux result on the next clock edge.
    | .storage, .input => c.instanceOutput .selection .result }

@[reducible] def body (signalType : SignalType) : ModuleBody :=
  ⟨context signalType, wiring signalType⟩

@[reducible] noncomputable def children (signalType : SignalType) :
    Contracts.Cycle.Certification.Children (body signalType)
  | .selection => Modules.Mux.certified signalType
  | .storage => Modules.Register.certified signalType

@[reducible] noncomputable def childStructure (signalType : SignalType) :=
  Contracts.Cycle.Certification.childStructure (children signalType)

@[reducible] def structuralChildren (signalType : SignalType) :
    (name : (instancePorts signalType).Name) →
      ModuleStructure ((instancePorts signalType).ports name)
  | .selection => Modules.Mux.moduleStructure signalType
  | .storage => Modules.Register.moduleStructure signalType

def moduleStructure (signalType : SignalType) :
    ModuleStructure (ports signalType) :=
  .composite (body signalType) (structuralChildren signalType)

theorem moduleStructure_eq (signalType : SignalType) :
    moduleStructure signalType =
      Contracts.Cycle.Certification.moduleStructure (body signalType) (children signalType) := by
  unfold moduleStructure Contracts.Cycle.Certification.moduleStructure
  congr
  funext child
  cases child <;> rfl

end Silean.Modules.EnabledRegister

namespace Silean.Modules.EnabledRegister.Naming

open Silean Silean.Naming

def portsWithNaming (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) :
    ModulePortsNaming (Modules.EnabledRegister.ports signalType) where
  inputs := ⟨fun | .value => "value" | .enable => "enable"⟩
  outputs := ⟨fun | .value => "value_out"⟩
  inputTypes := fun | .value => typeNaming | .enable => .bit
  outputTypes := fun | .value => typeNaming

def ports (signalType : SignalType) :
    ModulePortsNaming (Modules.EnabledRegister.ports signalType) :=
  portsWithNaming signalType (.positional signalType)

def namingWith (signalType : SignalType) (typeNaming : SignalTypeNaming signalType) :
    ModuleNaming (Modules.EnabledRegister.moduleStructure signalType) := by
  unfold Modules.EnabledRegister.moduleStructure
  exact .composite ⟨"enabled_register", "structural", [.shape signalType]⟩
    (portsWithNaming signalType typeNaming)
    (fun | .selection => "selection" | .storage => "storage")
    (fun
      | .selection => Modules.Mux.Naming.namingWith signalType typeNaming
      | .storage => Modules.Register.Naming.namingWith signalType typeNaming)

def naming (signalType : SignalType) :
    ModuleNaming (Modules.EnabledRegister.moduleStructure signalType) :=
  namingWith signalType (.positional signalType)

end Silean.Modules.EnabledRegister.Naming

namespace Silean.Modules.EnabledRegister
open Silean
/-! ## Exact cycle behavior and certification -/

inductive Rule | observe
deriving Enumeration
def outputRule (signalType : SignalType) :
    Contracts.Cycle.CycleOutputRule (Modules.EnabledRegister.ports signalType)
      (Modules.Register.stateMap signalType)
      { inputTypes := .nil, outputTypes := .cons signalType .nil } where
  readsInputs := .nil
  writesOutputs := (Modules.EnabledRegister.ports signalType).outputs.select .value
  target | (), state => (state .stored, ())
def stateRule (signalType : SignalType) :
    Contracts.Cycle.CycleStateRule (Modules.EnabledRegister.ports signalType)
      (Modules.Register.stateMap signalType) where
  inputTypes := .cons .bit (.cons signalType .nil)
  readsInputs := ((inputMap signalType).select .value).prepend .enable
  target := fun | (enable, (value, ())), state => fun
    | .stored => bif enable then value else state .stored
def cycleContract (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleContract (Modules.EnabledRegister.ports signalType) where
  state := Modules.Register.stateMap signalType
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .observe => ⟨_, outputRule signalType⟩
  stateRule := stateRule signalType
  outputCoverage := by rfl

abbrev selectionRule (signalType : SignalType) :
    Contracts.Cycle.Certification.RuleOccurrence (children signalType) :=
  ⟨.selection, Mux.Rule.select⟩

abbrev storageRule (signalType : SignalType) :
    Contracts.Cycle.Certification.RuleOccurrence (children signalType) :=
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
    Contracts.Cycle.Certification.OutputSchedule (body signalType) (children signalType)
      (cycleContract signalType) .observe :=
  .call (storageRule signalType)
    (by intro port member; cases port; cases member)
    (by simp)
  (.done (by
    intro output member
    cases output
    change Contracts.Cycle.Certification.outputAvailable ([storageRule signalType] :
      Contracts.Cycle.Certification.Availability (children signalType)) .storage .output
    exact ⟨Primitives.RegisterRule.observe, by simp, by simp⟩))

def stateSchedule (signalType : SignalType) :
    Contracts.Cycle.Certification.StateSchedule (body signalType) (children signalType) :=
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
  (.done (by
    intro child input member
    cases child with
    | selection =>
        rw [Mux.certified_cycleContract] at member
        simp [Mux.cycleContract, Mux.stateRule, Contracts.Cycle.CycleStateRule.empty,
          SignalSelection.labels] at member
    | storage =>
        cases input
        exact ⟨Mux.Rule.select, by simp, by simp⟩)))

def ruleSchedules (signalType : SignalType) :
    Contracts.Cycle.Certification.RuleSchedules (body signalType) (children signalType)
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
    apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_includes
    change selectionRule signalType ∈ (stateSchedule signalType).finalAvailability
    simp [stateSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]
  | storage =>
    change Register.Rule at rule
    cases rule
    apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_preserves
    apply Contracts.Cycle.Certification.RuleSchedules.mem_combineOutputs (ruleSchedules signalType) .observe
    change storageRule signalType ∈ (outputSchedule signalType).finalAvailability
    simp [outputSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]

theorem hasAtMostOneSolution (signalType : SignalType) :
    (Contracts.Cycle.Certification.moduleStructure (body signalType)
      (children signalType)).HasAtMostOneSolution :=
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
    (currentState : (Contracts.Cycle.Certification.moduleStructure (body signalType)
      (children signalType)).State) :
    ∃ proposal,
      (Contracts.Cycle.Certification.moduleStructure (body signalType)
        (children signalType)).IsSolution inputs currentState proposal := by
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
    (structuralState : (Contracts.Cycle.Certification.moduleStructure (body signalType)
      (children signalType)).State) : Prop :=
  (children signalType .storage).stateCorresponds contractState
    (structuralState .storage)

@[simp] theorem outputRule_holds_iff (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : (cycleContract signalType).state.Values)
    (outputs : (ports signalType).outputs.Values) :
    (outputRule signalType).Holds inputs state outputs ↔
      outputs .value = state .stored := by
  simp [Contracts.Cycle.CycleOutputRule.Holds, outputRule, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select]

private theorem implements (signalType : SignalType) :
    Contracts.Cycle.Implements (Contracts.Cycle.Certification.moduleStructure (body signalType)
      (children signalType)) (cycleContract signalType)
      (stateCorresponds signalType) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have storageMatches := Contracts.Cycle.Certification.childSolutionMatchesContract (children signalType)
    inputs structuralState proposal satisfies .storage contractState corresponds
  rcases (children signalType .selection).hasCorrespondingState
      (structuralState .selection) with ⟨selectionState, selectionCorresponds⟩
  have selectionState_eq : selectionState = SignalMap.emptyValues := by
    funext statePort
    exact nomatch statePort
  subst selectionState
  have selectionMatches := Contracts.Cycle.Certification.childSolutionMatchesContract (children signalType)
    inputs structuralState proposal satisfies .selection SignalMap.emptyValues
      selectionCorresponds
  have boundary := satisfies.1
  rcases proposal with ⟨outputs, childProposals⟩
  rcases storageMatches with ⟨storageEvaluates, storageNextCorresponds⟩
  rcases selectionMatches with ⟨selectionEvaluates, _⟩
  let storageNextState :=
    (children signalType .storage).cycleContract.stateRule.apply
      (ProposedValues.childInputs (body signalType) (childStructure signalType)
        inputs childProposals .storage) contractState
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
      rfl
    have selected := selectionEvaluates.1 Mux.Rule.select
    change (Mux.selectRule signalType).Holds _ SignalMap.emptyValues _ at selected
    simp [Contracts.Cycle.CycleOutputRule.Holds, Mux.selectRule, SignalSelection.Matches,
      SignalSelection.project, SignalMap.select, SignalSelection.prepend] at selected
    change (childProposals .selection).outputs .result =
      bif inputs .enable then inputs .value
        else (childProposals .storage).outputs .output at selected
    have storageCurrent := (Register.outputRule_holds_iff signalType _ _ _).mp
      (storageEvaluates.1 Primitives.RegisterRule.observe)
    funext statePort
    cases statePort
    rw [storageNextValue]
    simp only [cycleContract, stateRule, Contracts.Cycle.CycleStateRule.apply,
      SignalSelection.project, SignalSelection.prepend, SignalMap.select]
    change (childProposals .selection).outputs .result =
      bif inputs .enable then inputs .value else contractState .stored
    rw [selected, storageCurrent]

noncomputable def proofCertification (signalType : SignalType) :
    Contracts.Cycle.ModuleCycleCertification
      (Contracts.Cycle.Certification.moduleStructure (body signalType) (children signalType))
      (cycleContract signalType) where
  stateCorresponds := stateCorresponds signalType
  hasCorrespondingState := fun structuralState =>
    (children signalType .storage).hasCorrespondingState
      (structuralState .storage)
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
    ∃ proposal,
      (moduleStructure signalType).IsSolution inputs currentState proposal ∧
      ∀ other, (moduleStructure signalType).IsSolution inputs currentState other →
        other = proposal :=
  (certified signalType).hasExactlyOneStructuralResult inputs currentState
end Silean.Modules.EnabledRegister
