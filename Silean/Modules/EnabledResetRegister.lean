import Silean.CertifiedSchedule
import Silean.Modules.Mux
import Silean.Modules.ResetRegister

namespace Silean.Modules.EnabledResetRegister

open Silean

inductive Instance
  | selection
  | storage
deriving Enumeration

@[reducible] def instances (signalType : SignalType) : Instances :=
  EnumeratedMap.of Instance fun
    | .selection => Mux.ports signalType
    | .storage => ResetRegister.ports signalType

inductive Input
  | value
  | enable
  | reset
deriving Enumeration

inductive Output
  | value
deriving Enumeration

@[reducible] def inputMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of Input fun
    | .value => signalType
    | .enable | .reset => .bit

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
    | .value => (context signalType).instanceOutput .storage .value
  instanceInput
    | .selection, .select => (context signalType).moduleInput .enable
    | .selection, .whenFalse =>
        (context signalType).instanceOutput .storage .value
    | .selection, .whenTrue => (context signalType).moduleInput .value
    | .storage, .value =>
        (context signalType).instanceOutput .selection .result
    | .storage, .reset => (context signalType).moduleInput .reset

@[reducible] def body (signalType : SignalType) : ModuleBody :=
  ⟨context signalType, wiring signalType⟩

@[reducible] private noncomputable def children (signalType : SignalType)
    (resetValue : signalType.Denote) : Certified.Children (body signalType)
  | .selection => Mux.certified signalType
  | .storage => ResetRegister.certified signalType resetValue

@[reducible] private noncomputable def childStructure (signalType : SignalType)
    (resetValue : signalType.Denote) :=
  Certified.childStructure (children signalType resetValue)

@[reducible] private def structuralChildren (signalType : SignalType)
    (resetValue : signalType.Denote) :
    (name : (instances signalType).Name) →
      ModuleStructure ((instances signalType).ports name)
  | .selection => Mux.moduleStructure signalType
  | .storage => ResetRegister.moduleStructure signalType resetValue

def moduleStructure (signalType : SignalType) (resetValue : signalType.Denote) :
    ModuleStructure (ports signalType) :=
  .composite (body signalType) (structuralChildren signalType resetValue)

private theorem moduleStructure_eq (signalType : SignalType)
    (resetValue : signalType.Denote) :
    moduleStructure signalType resetValue =
      Certified.moduleStructure (body signalType)
        (children signalType resetValue) := by
  unfold moduleStructure Certified.moduleStructure
  congr
  funext child
  cases child <;> rfl

inductive Rule | observe
deriving Enumeration

def outputRule (signalType : SignalType) :
    CycleOutputRule (ports signalType) (Register.stateMap signalType)
      { inputTypes := .nil, outputTypes := .cons signalType .nil } where
  readsInputs := .nil
  writesOutputs := (outputMap signalType).select .value
  target | (), state => (state .stored, ())

def stateRule (signalType : SignalType) (resetValue : signalType.Denote) :
    CycleStateRule (ports signalType) (Register.stateMap signalType) where
  inputTypes := .cons .bit (.cons .bit (.cons signalType .nil))
  readsInputs := (((inputMap signalType).select .value).prepend .enable).prepend .reset
  target := fun | (reset, (enable, (value, ()))), state => fun
    | .stored => bif reset then resetValue else bif enable then value else state .stored

def cycleContract (signalType : SignalType) (resetValue : signalType.Denote) :
    ModuleCycleContract (ports signalType) where
  state := Register.stateMap signalType
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .observe => ⟨_, outputRule signalType⟩
  stateRule := stateRule signalType resetValue
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : (Register.stateMap signalType).Values)
    (outputs : (ports signalType).outputs.Values) :
    (outputRule signalType).Holds inputs state outputs ↔
      outputs .value = state .stored := by
  simp [CycleOutputRule.Holds, outputRule, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select]

@[simp] theorem stateRule_apply_stored (signalType : SignalType)
    (resetValue : signalType.Denote)
    (inputs : (ports signalType).inputs.Values)
    (state : (Register.stateMap signalType).Values) :
    (stateRule signalType resetValue).apply inputs state .stored =
      bif inputs .reset then resetValue
      else bif inputs .enable then inputs .value else state .stored := by
  rfl

theorem next_stored_of_reset (signalType : SignalType)
    (resetValue : signalType.Denote)
    (inputs : (ports signalType).inputs.Values)
    (state : (Register.stateMap signalType).Values)
    (reset : inputs .reset = true) :
    (stateRule signalType resetValue).apply inputs state .stored = resetValue := by
  rw [stateRule_apply_stored, reset]
  rfl

theorem next_stored_of_enabled (signalType : SignalType)
    (resetValue : signalType.Denote)
    (inputs : (ports signalType).inputs.Values)
    (state : (Register.stateMap signalType).Values)
    (notReset : inputs .reset = false) (enabled : inputs .enable = true) :
    (stateRule signalType resetValue).apply inputs state .stored = inputs .value := by
  rw [stateRule_apply_stored, notReset, enabled]
  rfl

theorem next_stored_of_disabled (signalType : SignalType)
    (resetValue : signalType.Denote)
    (inputs : (ports signalType).inputs.Values)
    (state : (Register.stateMap signalType).Values)
    (notReset : inputs .reset = false) (disabled : inputs .enable = false) :
    (stateRule signalType resetValue).apply inputs state .stored = state .stored := by
  rw [stateRule_apply_stored, notReset, disabled]
  rfl

private abbrev selectionRule (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Certified.RuleOccurrence (children signalType resetValue) :=
  ⟨.selection, Mux.Rule.select⟩

private abbrev storageRule (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Certified.RuleOccurrence (children signalType resetValue) :=
  ⟨.storage, ResetRegister.Rule.observe⟩

@[simp] private theorem selectionRule_reads (signalType : SignalType)
    (resetValue : signalType.Denote) :
    (selectionRule signalType resetValue).reads =
      [.select, .whenFalse, .whenTrue] := rfl

@[simp] private theorem selectionRule_writes (signalType : SignalType)
    (resetValue : signalType.Denote) :
    (selectionRule signalType resetValue).writes = [.result] := rfl

@[simp] private theorem storageRule_reads (signalType : SignalType)
    (resetValue : signalType.Denote) :
    (storageRule signalType resetValue).reads = [] := rfl

@[simp] private theorem storageRule_writes (signalType : SignalType)
    (resetValue : signalType.Denote) :
    (storageRule signalType resetValue).writes = [.value] := rfl

private def outputSchedule (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Certified.OutputSchedule (body signalType) (children signalType resetValue)
      (cycleContract signalType resetValue) .observe :=
  .call (storageRule signalType resetValue)
    (by
      intro port member
      rw [storageRule_reads] at member
      cases member)
    (by simp)
  (.done (by
    intro output member
    cases output
    change Certified.outputAvailable ([storageRule signalType resetValue] :
      Certified.Availability (children signalType resetValue)) .storage .value
    exact ⟨ResetRegister.Rule.observe, by simp, by simp⟩))

private def stateSchedule (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Certified.StateSchedule (body signalType) (children signalType resetValue) :=
  .call (storageRule signalType resetValue)
    (by
      intro port member
      rw [storageRule_reads] at member
      cases member)
    (by simp)
  (.call (selectionRule signalType resetValue)
    (by
      intro input member
      cases input with
      | select | whenTrue => trivial
      | whenFalse =>
          exact ⟨ResetRegister.Rule.observe, by simp, by simp⟩)
    (by simp)
  (.done (by
    intro child input member
    cases child with
    | selection =>
        rw [Mux.certified_cycleContract] at member
        simp [Mux.cycleContract, Mux.stateRule, CycleStateRule.empty,
          SignalSelection.labels] at member
    | storage =>
        cases input with
        | value => exact ⟨Mux.Rule.select, by simp, by simp⟩
        | reset => trivial)))

private def ruleSchedules (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Certified.RuleSchedules (body signalType) (children signalType resetValue)
      (cycleContract signalType resetValue) where
  output | .observe => outputSchedule signalType resetValue
  state := stateSchedule signalType resetValue

private theorem coversChildren (signalType : SignalType)
    (resetValue : signalType.Denote) :
    (ruleSchedules signalType resetValue).CoversChildren := by
  intro child rule
  cases child with
  | selection =>
      change Mux.Rule at rule
      cases rule
      apply Certified.RuleSchedules.Combined.add_includes
      change selectionRule signalType resetValue ∈
        (stateSchedule signalType resetValue).finalAvailability
      simp [stateSchedule, Certified.Schedule.finalAvailability]
  | storage =>
      change ResetRegister.Rule at rule
      cases rule
      apply Certified.RuleSchedules.Combined.add_preserves
      apply Certified.RuleSchedules.mem_combineOutputs
        (ruleSchedules signalType resetValue) .observe
      change storageRule signalType resetValue ∈
        (outputSchedule signalType resetValue).finalAvailability
      simp [outputSchedule, Certified.Schedule.finalAvailability]

private theorem hasAtMostOneSolution (signalType : SignalType)
    (resetValue : signalType.Denote) :
    (Certified.moduleStructure (body signalType)
      (children signalType resetValue)).HasAtMostOneSolution :=
  (ruleSchedules signalType resetValue).hasAtMostOneSolution
    (coversChildren signalType resetValue)

private def selectionInputs (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values) (stored : signalType.Denote) :
    (Mux.ports signalType).inputs.Values
  | .select => inputs .enable
  | .whenFalse => stored
  | .whenTrue => inputs .value

private noncomputable def storageInputs (signalType : SignalType)
    (resetValue : signalType.Denote)
    (inputs : (ports signalType).inputs.Values)
    (selection : ProposedValues
      (children signalType resetValue .selection).moduleStructure) :
    (ResetRegister.ports signalType).inputs.Values
  | .value => selection.outputs .result
  | .reset => inputs .reset

private theorem hasStructuralResult (signalType : SignalType)
    (resetValue : signalType.Denote)
    (inputs : (ports signalType).inputs.Values)
    (currentState : (Certified.moduleStructure (body signalType)
      (children signalType resetValue)).State) :
    ∃ proposal, (Certified.moduleStructure (body signalType)
      (children signalType resetValue)).IsSolution inputs currentState proposal := by
  rcases (children signalType resetValue .storage).hasCorrespondingState
      (currentState .storage) with ⟨storageState, storageCorresponds⟩
  rcases (children signalType resetValue .selection).hasStructuralResult
      (selectionInputs signalType inputs (storageState .stored))
      (currentState .selection) with ⟨selection, selectionSatisfies⟩
  rcases (children signalType resetValue .storage).hasStructuralResult
      (storageInputs signalType resetValue inputs selection)
      (currentState .storage) with ⟨storage, storageSatisfies⟩
  have storageOutput : storage.outputs .value = storageState .stored := by
    rcases (children signalType resetValue .storage).implements
        (storageInputs signalType resetValue inputs selection) storageState
        (currentState .storage) storage storageCorresponds storageSatisfies with
      ⟨nextState, evaluates, nextCorresponds⟩
    exact (ResetRegister.outputRule_holds_iff signalType _ _ _).mp
      (evaluates.1 ResetRegister.Rule.observe)
  let childProposals : (name : Instance) →
      ProposedValues (childStructure signalType resetValue name)
    | .selection => selection
    | .storage => storage
  let outputs : (ports signalType).outputs.Values := fun
    | .value => storage.outputs .value
  refine ⟨ProposedValues.composite outputs childProposals, ?_⟩
  constructor
  · intro output; cases output; rfl
  · intro child
    cases child with
    | selection =>
        change (children signalType resetValue .selection).moduleStructure.IsSolution
          (ProposedValues.childInputs (body signalType)
            (childStructure signalType resetValue) inputs childProposals .selection)
          (currentState .selection) selection
        rw [show ProposedValues.childInputs (body signalType)
          (childStructure signalType resetValue) inputs childProposals .selection =
            selectionInputs signalType inputs (storageState .stored) by
          funext port
          cases port with
          | select | whenTrue => rfl
          | whenFalse => exact storageOutput]
        exact selectionSatisfies
    | storage =>
        change (children signalType resetValue .storage).moduleStructure.IsSolution
          (ProposedValues.childInputs (body signalType)
            (childStructure signalType resetValue) inputs childProposals .storage)
          (currentState .storage) storage
        rw [show ProposedValues.childInputs (body signalType)
          (childStructure signalType resetValue) inputs childProposals .storage =
            storageInputs signalType resetValue inputs selection by
          funext port; cases port <;> rfl]
        exact storageSatisfies

private def stateCorresponds (signalType : SignalType)
    (resetValue : signalType.Denote)
    (contractState : (cycleContract signalType resetValue).state.Values)
    (structuralState : (Certified.moduleStructure (body signalType)
      (children signalType resetValue)).State) : Prop :=
  (children signalType resetValue .storage).stateCorresponds contractState
    (structuralState .storage)

private theorem implements (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Implements (Certified.moduleStructure (body signalType)
      (children signalType resetValue)) (cycleContract signalType resetValue)
      (stateCorresponds signalType resetValue) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have storageMatches := Certified.childSolutionMatchesContract
    (children signalType resetValue) inputs structuralState proposal satisfies
      .storage contractState corresponds
  rcases (children signalType resetValue .selection).hasCorrespondingState
      (structuralState .selection) with ⟨selectionState, selectionCorresponds⟩
  have selectionState_eq : selectionState = SignalMap.emptyValues := by
    funext statePort
    exact nomatch statePort
  subst selectionState
  have selectionMatches := Certified.childSolutionMatchesContract
    (children signalType resetValue) inputs structuralState proposal satisfies
      .selection SignalMap.emptyValues selectionCorresponds
  rcases proposal with ⟨outputs, childProposals⟩
  rcases storageMatches with ⟨storageEvaluates, storageNextCorresponds⟩
  rcases selectionMatches with ⟨selectionEvaluates, _⟩
  let storageNextState :=
    (children signalType resetValue .storage).cycleContract.stateRule.apply
      (ProposedValues.childInputs (body signalType)
        (childStructure signalType resetValue) inputs childProposals .storage)
      contractState
  refine ⟨storageNextState, ?_, storageNextCorresponds⟩
  constructor
  · intro name
    cases name
    change (outputRule signalType).Holds inputs contractState _
    rw [outputRule_holds_iff]
    exact (satisfies.1 .value).trans
      ((ResetRegister.outputRule_holds_iff signalType _ _ _).mp
        (storageEvaluates.1 ResetRegister.Rule.observe))
  · have storageNextValue : storageNextState .stored =
        bif inputs .reset then resetValue
        else (childProposals .selection).outputs .result := by
      exact ResetRegister.stateRule_apply_stored signalType resetValue _ _
    have selected := (Mux.selectRule_holds_iff signalType _ _ _).mp
      (selectionEvaluates.1 Mux.Rule.select)
    change (childProposals .selection).outputs .result =
      bif inputs .enable then inputs .value
        else (childProposals .storage).outputs .value at selected
    have storageCurrent := (ResetRegister.outputRule_holds_iff signalType _ _ _).mp
      (storageEvaluates.1 ResetRegister.Rule.observe)
    funext statePort
    cases statePort
    rw [storageNextValue]
    change (bif inputs .reset then resetValue
      else (childProposals .selection).outputs .result) =
      bif inputs .reset then resetValue
      else bif inputs .enable then inputs .value else contractState .stored
    rw [selected, storageCurrent]

private noncomputable def proofCertification (signalType : SignalType)
    (resetValue : signalType.Denote) :
    ModuleCycleCertification
      (Certified.moduleStructure (body signalType) (children signalType resetValue))
      (cycleContract signalType resetValue) where
  stateCorresponds := stateCorresponds signalType resetValue
  hasCorrespondingState := fun structuralState =>
    (children signalType resetValue .storage).hasCorrespondingState
      (structuralState .storage)
  hasStructuralResult := hasStructuralResult signalType resetValue
  structuralResultUnique := hasAtMostOneSolution signalType resetValue
  implements := implements signalType resetValue

private noncomputable opaque certification (signalType : SignalType)
    (resetValue : signalType.Denote) :
    ModuleCycleCertification (moduleStructure signalType resetValue)
      (cycleContract signalType resetValue) :=
  (proofCertification signalType resetValue).transportStructure
    (moduleStructure_eq signalType resetValue).symm

noncomputable def certified (signalType : SignalType)
    (resetValue : signalType.Denote) : ModuleCycleCertified (ports signalType) :=
  (certification signalType resetValue).bundle

@[simp] theorem certified_moduleStructure (signalType : SignalType)
    (resetValue : signalType.Denote) :
    (certified signalType resetValue).moduleStructure =
      moduleStructure signalType resetValue := rfl

@[simp] theorem certified_cycleContract (signalType : SignalType)
    (resetValue : signalType.Denote) :
    (certified signalType resetValue).cycleContract =
      cycleContract signalType resetValue := rfl

end Silean.Modules.EnabledResetRegister

namespace Silean.Modules.EnabledResetRegister.Naming

open Silean Silean.Naming

def portsWithNaming (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) :
    ModulePortsNaming (Modules.EnabledResetRegister.ports signalType) where
  inputs := ⟨fun
    | .value => "value"
    | .enable => "enable"
    | .reset => "reset"⟩
  outputs := ⟨fun | .value => "value_out"⟩
  inputTypes := fun | .value => typeNaming | .enable | .reset => .bit
  outputTypes := fun | .value => typeNaming

def ports (signalType : SignalType) :
    ModulePortsNaming (Modules.EnabledResetRegister.ports signalType) :=
  portsWithNaming signalType (.positional signalType)

def namingWith (signalType : SignalType) (resetValue : signalType.Denote)
    (typeNaming : SignalTypeNaming signalType) :
    ModuleNaming
      (Modules.EnabledResetRegister.moduleStructure signalType resetValue) := by
  unfold Modules.EnabledResetRegister.moduleStructure
  exact .composite
    ⟨"enabled_reset_register", "structural",
      .shape signalType :: Modules.Constant.Naming.parameters signalType resetValue⟩
    (portsWithNaming signalType typeNaming)
    (fun | .selection => "selection" | .storage => "storage")
    (fun
      | .selection => Modules.Mux.Naming.namingWith signalType typeNaming
      | .storage => Modules.ResetRegister.Naming.namingWith
          signalType resetValue typeNaming)

def naming (signalType : SignalType) (resetValue : signalType.Denote) :
    ModuleNaming
      (Modules.EnabledResetRegister.moduleStructure signalType resetValue) :=
  namingWith signalType resetValue (.positional signalType)

end Silean.Modules.EnabledResetRegister.Naming
