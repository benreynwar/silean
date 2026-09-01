import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Modules.Mux
import Silean.Modules.ResetRegister

namespace Silean.Modules.EnabledResetRegister

open Silean

/-! ## Hardware structure -/

/-- A register which resets to a fixed value, loads a new value when enabled,
and otherwise retains its current value. -/
inductive Instance
  /-- Chooses between the new input and the stored value. -/
  | selection
  /-- Applies reset and stores the selected value. -/
  | storage
deriving Enumeration

@[reducible] def instancePorts (signalType : SignalType) : InstancePorts :=
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
  instancePorts := instancePorts signalType

def wiring (signalType : SignalType) :
    Wiring (context signalType).ports (context signalType).instancePorts :=
  let c := context signalType
  { moduleOutput := fun
    -- The stored value is exposed directly.
    | .value => c.instanceOutput .storage .value
    instanceInput := fun
    -- Select the new input when enabled, or feed the stored value back.
    | .selection, .select => c.moduleInput .enable
    | .selection, .whenFalse =>
        c.instanceOutput .storage .value
    | .selection, .whenTrue => c.moduleInput .value
    -- The resettable register stores the mux result.
    | .storage, .value =>
        c.instanceOutput .selection .result
    | .storage, .reset => c.moduleInput .reset }

@[reducible] def body (signalType : SignalType) : ModuleBody :=
  ⟨context signalType, wiring signalType⟩

@[reducible] private def childContracts (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Contracts.Cycle.ChildCycleContracts (body signalType)
  | .selection => Mux.cycleContract signalType
  | .storage => ResetRegister.cycleContract signalType resetValue

@[reducible] private def structuralChildren (signalType : SignalType)
    (resetValue : signalType.Denote) :
    (name : (instancePorts signalType).Name) →
      ModuleStructure ((instancePorts signalType).ports name)
  | .selection => Mux.moduleStructure signalType
  | .storage => ResetRegister.moduleStructure signalType resetValue

def moduleStructure (signalType : SignalType) (resetValue : signalType.Denote) :
    ModuleStructure (ports signalType) :=
  .composite (body signalType) (structuralChildren signalType resetValue)

@[reducible] private noncomputable def certifiedChildren (signalType : SignalType)
    (resetValue : signalType.Denote) :
    (name : (instancePorts signalType).Name) →
      Contracts.Cycle.ModuleCycleCertifiedStructure
        (childContracts signalType resetValue name)
  | .selection => Mux.certifiedStructure signalType
  | .storage =>
      ⟨(ResetRegister.certified signalType resetValue).moduleStructure,
        (ResetRegister.certified signalType resetValue).certification⟩

/-! ## Exact cycle behavior and certification -/

inductive Rule | observe
deriving Enumeration

def outputRule (signalType : SignalType) :
    Contracts.Cycle.CycleOutputRule (ports signalType) (Register.stateMap signalType)
      { inputTypes := .nil, outputTypes := .cons signalType .nil } where
  readsInputs := .nil
  writesOutputs := (outputMap signalType).select .value
  target | (), state => (state .stored, ())

def stateRule (signalType : SignalType) (resetValue : signalType.Denote) :
    Contracts.Cycle.CycleStateRule (ports signalType) (Register.stateMap signalType) where
  inputTypes := .cons .bit (.cons .bit (.cons signalType .nil))
  readsInputs := (((inputMap signalType).select .value).prepend .enable).prepend .reset
  target := fun | (reset, (enable, (value, ()))), state => fun
    | .stored => bif reset then resetValue else bif enable then value else state .stored

def cycleContract (signalType : SignalType) (resetValue : signalType.Denote) :
    Contracts.Cycle.ModuleCycleContract (ports signalType) where
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
  simp [Contracts.Cycle.CycleOutputRule.Holds, outputRule, SignalSelection.Matches,
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
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body signalType) (childContracts signalType resetValue) :=
  ⟨.selection, Mux.Rule.select⟩

private abbrev storageRule (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (body signalType) (childContracts signalType resetValue) :=
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
    Contracts.Cycle.Certification.Layer.OutputSchedule
      (body signalType) (childContracts signalType resetValue)
      (cycleContract signalType resetValue) .observe :=
  .call (storageRule signalType resetValue)
    (by
      intro port member
      simp [storageRule_reads] at member)
    (by simp)
  (.done (by
    intro output member
    cases output
    change Contracts.Cycle.Certification.Layer.outputAvailable
      ([storageRule signalType resetValue] :
        Contracts.Cycle.Certification.Layer.Availability
          (body signalType) (childContracts signalType resetValue)) .storage .value
    exact ⟨ResetRegister.Rule.observe, by simp, by simp⟩))

private def stateSchedule (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Contracts.Cycle.Certification.Layer.StateSchedule
      (body signalType) (childContracts signalType resetValue) :=
  .call (storageRule signalType resetValue)
    (by
      intro port member
      simp [storageRule_reads] at member)
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
        simp [childContracts, Mux.cycleContract, Mux.stateRule, Contracts.Cycle.CycleStateRule.empty,
          SignalSelection.labels] at member
    | storage =>
        cases input with
        | value => exact ⟨Mux.Rule.select, by simp, by simp⟩
        | reset => trivial)))

private def ruleSchedules (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Contracts.Cycle.Certification.Layer.RuleSchedules
      (body signalType) (childContracts signalType resetValue)
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
      left
      change selectionRule signalType resetValue ∈
        (stateSchedule signalType resetValue).finalAvailability
      simp [stateSchedule, Contracts.Cycle.Certification.Layer.Schedule.finalAvailability]
  | storage =>
      change ResetRegister.Rule at rule
      cases rule
      right
      refine ⟨.observe, ?_⟩
      change storageRule signalType resetValue ∈
        (outputSchedule signalType resetValue).finalAvailability
      simp [outputSchedule, Contracts.Cycle.Certification.Layer.Schedule.finalAvailability]

section LayerCertification

variable (signalType : SignalType) (resetValue : signalType.Denote)
  (layerChildren : Contracts.Cycle.Certification.Layer.ChildStructures
    (body signalType) (childContracts signalType resetValue))

private def stateCorresponds
    (contractState : (cycleContract signalType resetValue).state.Values)
    (structuralState :
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body signalType) layerChildren).State) : Prop :=
  (layerChildren .storage).certification.stateCorresponds
    contractState (structuralState .storage)

private theorem implements :
    Contracts.Cycle.Implements
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body signalType) layerChildren)
      (cycleContract signalType resetValue)
      (stateCorresponds signalType resetValue layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have storageMatches := Contracts.Cycle.Certification.Layer.childSolutionMatchesContract
    layerChildren
      inputs structuralState proposal satisfies
      .storage contractState corresponds
  have selectionStateSubsingleton :
      Subsingleton (childContracts signalType resetValue .selection).state.Values := by
    change Subsingleton emptySignalMap.Values
    infer_instance
  have selectionMatches :=
    letI := selectionStateSubsingleton
    Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren
      inputs structuralState proposal satisfies
      .selection SignalMap.emptyValues
  rcases proposal with ⟨outputs, childProposals⟩
  rcases storageMatches with ⟨storageEvaluates, storageNextCorresponds⟩
  rcases selectionMatches with ⟨selectionEvaluates, _⟩
  let storageNextState :=
    (childContracts signalType resetValue .storage).stateRule.apply
      (ProposedValues.childInputs (body signalType)
        (fun child => (layerChildren child).moduleStructure)
        inputs childProposals .storage)
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

end LayerCertification

/-- The enabled-reset-register wiring implements its contract for any mux and
reset-register implementations satisfying their public contracts. -/
noncomputable opaque certifiedLayer (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Contracts.Cycle.ModuleCycleCertifiedLayer (body signalType)
      (childContracts signalType resetValue)
      (cycleContract signalType resetValue) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (ruleSchedules signalType resetValue) (coversChildren signalType resetValue)
    (stateCorresponds signalType resetValue)
    (fun children structuralState =>
      (children .storage).certification.hasCorrespondingState
        (structuralState .storage))
    (implements signalType resetValue)

private noncomputable opaque certification (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure signalType resetValue)
      (cycleContract signalType resetValue) :=
  (certifiedLayer signalType resetValue).certifyComposite
    (structuralChildren signalType resetValue)
    (certifiedChildren signalType resetValue)
    (by
      intro child
      cases child with
      | selection => exact Mux.certifiedStructure_moduleStructure signalType
      | storage => exact ResetRegister.certified_moduleStructure signalType resetValue)

noncomputable def certified (signalType : SignalType)
    (resetValue : signalType.Denote) : Contracts.Cycle.ModuleCycleCertified (ports signalType) :=
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
