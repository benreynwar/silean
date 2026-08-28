import Silean.Contracts.Cycle.CycleSchedule
import Silean.Modules.Constant
import Silean.Modules.Mux
import Silean.Modules.Register

namespace Silean.Modules.ResetRegister

open Silean

/-! ## Hardware structure -/

/-- A register which stores `value`, except that reset selects a fixed value. -/
inductive Instance
  /-- Produces the value loaded during reset. -/
  | resetValue
  /-- Chooses between the ordinary input and reset value. -/
  | selection
  /-- Holds the selected value across cycles. -/
  | storage
deriving Enumeration

@[reducible] def instancePorts (signalType : SignalType)
    (_resetValue : signalType.Denote) : InstancePorts :=
  EnumeratedMap.of Instance fun
    | .resetValue => Constant.ports signalType
    | .selection => Mux.ports signalType
    | .storage => Register.ports signalType

inductive Input
  | value
  | reset
deriving Enumeration

inductive Output
  | value
deriving Enumeration

@[reducible] def inputMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of Input fun
    | .value => signalType
    | .reset => .bit

@[reducible] def outputMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of Output fun | .value => signalType

@[reducible] def ports (signalType : SignalType) : ModulePorts :=
  ⟨inputMap signalType, outputMap signalType⟩

@[reducible] def context (signalType : SignalType)
    (resetValue : signalType.Denote) : EndpointContext where
  ports := ports signalType
  instancePorts := instancePorts signalType resetValue

def wiring (signalType : SignalType) (resetValue : signalType.Denote) :
    Wiring (context signalType resetValue).ports
      (context signalType resetValue).instancePorts :=
  let c := context signalType resetValue
  { moduleOutput := fun
    -- The stored value is exposed directly.
    | .value => c.instanceOutput .storage .output
    instanceInput := fun
    | .resetValue, impossible => nomatch impossible
    -- Reset selects the constant; otherwise select the ordinary input.
    | .selection, .select =>
        c.moduleInput .reset
    | .selection, .whenFalse =>
        c.moduleInput .value
    | .selection, .whenTrue =>
        c.instanceOutput .resetValue .output
    -- Store the selected value on the next clock edge.
    | .storage, .input =>
        c.instanceOutput .selection .result }

@[reducible] def body (signalType : SignalType)
    (resetValue : signalType.Denote) : ModuleBody :=
  ⟨context signalType resetValue, wiring signalType resetValue⟩

@[reducible] private noncomputable def children (signalType : SignalType)
    (resetValue : signalType.Denote) : Contracts.Cycle.Certification.Children (body signalType resetValue)
  | .resetValue => Constant.certified signalType resetValue
  | .selection => Mux.certified signalType
  | .storage => Register.certified signalType

@[reducible] private noncomputable def childStructure (signalType : SignalType)
    (resetValue : signalType.Denote) :=
  Contracts.Cycle.Certification.childStructure (children signalType resetValue)

@[reducible] private def structuralChildren (signalType : SignalType)
    (resetValue : signalType.Denote) :
    (name : (instancePorts signalType resetValue).Name) →
      ModuleStructure ((instancePorts signalType resetValue).ports name)
  | .resetValue => Constant.moduleStructure signalType resetValue
  | .selection => Mux.moduleStructure signalType
  | .storage => Register.moduleStructure signalType

def moduleStructure (signalType : SignalType) (resetValue : signalType.Denote) :
    ModuleStructure (ports signalType) :=
  .composite (body signalType resetValue) (structuralChildren signalType resetValue)

private theorem moduleStructure_eq (signalType : SignalType)
    (resetValue : signalType.Denote) :
    moduleStructure signalType resetValue =
      Contracts.Cycle.Certification.moduleStructure (body signalType resetValue)
        (children signalType resetValue) := by
  unfold moduleStructure Contracts.Cycle.Certification.moduleStructure
  congr
  funext child
  cases child <;> rfl

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
  inputTypes := .cons .bit (.cons signalType .nil)
  readsInputs := ((inputMap signalType).select .value).prepend .reset
  target := fun | (reset, (value, ())), _ => fun
    | .stored => bif reset then resetValue else value

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
      bif inputs .reset then resetValue else inputs .value := by
  rfl

theorem next_stored_of_reset (signalType : SignalType)
    (resetValue : signalType.Denote)
    (inputs : (ports signalType).inputs.Values)
    (state : (Register.stateMap signalType).Values)
    (reset : inputs .reset = true) :
    (stateRule signalType resetValue).apply inputs state .stored = resetValue := by
  rw [stateRule_apply_stored, reset]
  rfl

theorem next_stored_of_not_reset (signalType : SignalType)
    (resetValue : signalType.Denote)
    (inputs : (ports signalType).inputs.Values)
    (state : (Register.stateMap signalType).Values)
    (notReset : inputs .reset = false) :
    (stateRule signalType resetValue).apply inputs state .stored = inputs .value := by
  rw [stateRule_apply_stored, notReset]
  rfl

private abbrev constantRule (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Contracts.Cycle.Certification.RuleOccurrence (children signalType resetValue) :=
  ⟨.resetValue, Primitives.ConstantRule.apply⟩

private abbrev selectionRule (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Contracts.Cycle.Certification.RuleOccurrence (children signalType resetValue) :=
  ⟨.selection, Mux.Rule.select⟩

private abbrev storageRule (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Contracts.Cycle.Certification.RuleOccurrence (children signalType resetValue) :=
  ⟨.storage, Primitives.RegisterRule.observe⟩

@[simp] private theorem constantRule_reads (signalType : SignalType)
    (resetValue : signalType.Denote) :
    (constantRule signalType resetValue).reads = [] := rfl

@[simp] private theorem constantRule_writes (signalType : SignalType)
    (resetValue : signalType.Denote) :
    (constantRule signalType resetValue).writes = [.output] := rfl

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
    (storageRule signalType resetValue).writes = [.output] := rfl

private def outputSchedule (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Contracts.Cycle.Certification.OutputSchedule (body signalType resetValue)
      (children signalType resetValue) (cycleContract signalType resetValue) .observe :=
  .call (storageRule signalType resetValue)
    (by intro port member; cases port; cases member)
    (by simp)
  (.done (by
    intro output member
    cases output
    change Contracts.Cycle.Certification.outputAvailable ([storageRule signalType resetValue] :
      Contracts.Cycle.Certification.Availability (children signalType resetValue)) .storage .output
    exact ⟨Primitives.RegisterRule.observe, by simp, by simp⟩))

private def stateSchedule (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Contracts.Cycle.Certification.StateSchedule (body signalType resetValue)
      (children signalType resetValue) :=
  .call (constantRule signalType resetValue)
    (by intro input; exact nomatch input)
    (by simp)
  (.call (selectionRule signalType resetValue)
    (by
      intro input member
      cases input with
      | select | whenFalse => trivial
      | whenTrue =>
          change Contracts.Cycle.Certification.outputAvailable
            ([constantRule signalType resetValue] :
              Contracts.Cycle.Certification.Availability (children signalType resetValue))
            .resetValue .output
          exact ⟨Primitives.ConstantRule.apply, by simp, by simp⟩)
    (by simp)
  (.done (by
    intro child input member
    cases child with
    | resetValue => exact nomatch input
    | selection =>
        rw [Mux.certified_cycleContract] at member
        simp [Mux.cycleContract, Mux.stateRule, Contracts.Cycle.CycleStateRule.empty,
          SignalSelection.labels] at member
    | storage =>
        cases input
        change Contracts.Cycle.Certification.outputAvailable
          ([selectionRule signalType resetValue,
            constantRule signalType resetValue] :
            Contracts.Cycle.Certification.Availability (children signalType resetValue))
          .selection .result
        exact ⟨Mux.Rule.select, by simp, by simp⟩)))

private def ruleSchedules (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Contracts.Cycle.Certification.RuleSchedules (body signalType resetValue)
      (children signalType resetValue) (cycleContract signalType resetValue) where
  output | .observe => outputSchedule signalType resetValue
  state := stateSchedule signalType resetValue

private theorem coversChildren (signalType : SignalType)
    (resetValue : signalType.Denote) :
    (ruleSchedules signalType resetValue).CoversChildren := by
  intro child rule
  cases child with
  | resetValue =>
      change Primitives.ConstantRule at rule
      cases rule
      apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_includes
      change constantRule signalType resetValue ∈
        (stateSchedule signalType resetValue).finalAvailability
      simp [stateSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]
  | selection =>
      change Mux.Rule at rule
      cases rule
      apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_includes
      change selectionRule signalType resetValue ∈
        (stateSchedule signalType resetValue).finalAvailability
      simp [stateSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]
  | storage =>
      change Register.Rule at rule
      cases rule
      apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_preserves
      apply Contracts.Cycle.Certification.RuleSchedules.mem_combineOutputs
        (ruleSchedules signalType resetValue) .observe
      change storageRule signalType resetValue ∈
        (outputSchedule signalType resetValue).finalAvailability
      simp [outputSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]

private theorem hasAtMostOneSolution (signalType : SignalType)
    (resetValue : signalType.Denote) :
    (Contracts.Cycle.Certification.moduleStructure (body signalType resetValue)
      (children signalType resetValue)).HasAtMostOneSolution :=
  (ruleSchedules signalType resetValue).hasAtMostOneSolution
    (coversChildren signalType resetValue)

private noncomputable def selectionInputs (signalType : SignalType)
    (resetValue : signalType.Denote)
    (inputs : (ports signalType).inputs.Values)
    (constant : ProposedValues
      (children signalType resetValue .resetValue).moduleStructure) :
    (Mux.ports signalType).inputs.Values
  | .select => inputs .reset
  | .whenFalse => inputs .value
  | .whenTrue => constant.outputs .output

private noncomputable def storageInputs (signalType : SignalType)
    (resetValue : signalType.Denote)
    (selection : ProposedValues
      (children signalType resetValue .selection).moduleStructure) :
    (Register.ports signalType).inputs.Values
  | .input => selection.outputs .result

private theorem hasStructuralResult (signalType : SignalType)
    (resetValue : signalType.Denote)
    (inputs : (ports signalType).inputs.Values)
    (currentState : (Contracts.Cycle.Certification.moduleStructure (body signalType resetValue)
      (children signalType resetValue)).State) :
    ∃ proposal, (Contracts.Cycle.Certification.moduleStructure (body signalType resetValue)
      (children signalType resetValue)).IsSolution inputs currentState proposal := by
  rcases (children signalType resetValue .resetValue).hasStructuralResult
      (fun impossible => nomatch impossible) (currentState .resetValue) with
    ⟨constant, constantSatisfies⟩
  rcases (children signalType resetValue .selection).hasStructuralResult
      (selectionInputs signalType resetValue inputs constant) (currentState .selection) with
    ⟨selection, selectionSatisfies⟩
  rcases (children signalType resetValue .storage).hasStructuralResult
      (storageInputs signalType resetValue selection) (currentState .storage) with
    ⟨storage, storageSatisfies⟩
  let childProposals : (name : Instance) →
      ProposedValues (childStructure signalType resetValue name)
    | .resetValue => constant
    | .selection => selection
    | .storage => storage
  let outputs : (ports signalType).outputs.Values := fun
    | .value => storage.outputs .output
  refine ⟨ProposedValues.composite outputs childProposals, ?_⟩
  constructor
  · intro output; cases output; rfl
  · intro child
    cases child with
    | resetValue =>
        change (children signalType resetValue .resetValue).moduleStructure.IsSolution
          (ProposedValues.childInputs (body signalType resetValue)
            (childStructure signalType resetValue) inputs childProposals .resetValue)
          (currentState .resetValue) constant
        rw [show ProposedValues.childInputs (body signalType resetValue)
          (childStructure signalType resetValue) inputs childProposals .resetValue =
            (fun impossible => nomatch impossible) by
          funext input; exact nomatch input]
        exact constantSatisfies
    | selection =>
        change (children signalType resetValue .selection).moduleStructure.IsSolution
          (ProposedValues.childInputs (body signalType resetValue)
            (childStructure signalType resetValue) inputs childProposals .selection)
          (currentState .selection) selection
        rw [show ProposedValues.childInputs (body signalType resetValue)
          (childStructure signalType resetValue) inputs childProposals .selection =
            selectionInputs signalType resetValue inputs constant by
          funext port; cases port <;> rfl]
        exact selectionSatisfies
    | storage =>
        change (children signalType resetValue .storage).moduleStructure.IsSolution
          (ProposedValues.childInputs (body signalType resetValue)
            (childStructure signalType resetValue) inputs childProposals .storage)
          (currentState .storage) storage
        rw [show ProposedValues.childInputs (body signalType resetValue)
          (childStructure signalType resetValue) inputs childProposals .storage =
            storageInputs signalType resetValue selection by
          funext port; cases port; rfl]
        exact storageSatisfies

private def stateCorresponds (signalType : SignalType)
    (resetValue : signalType.Denote)
    (contractState : (cycleContract signalType resetValue).state.Values)
    (structuralState : (Contracts.Cycle.Certification.moduleStructure (body signalType resetValue)
      (children signalType resetValue)).State) : Prop :=
  (children signalType resetValue .storage).stateCorresponds contractState
    (structuralState .storage)

private theorem implements (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Contracts.Cycle.Implements (Contracts.Cycle.Certification.moduleStructure (body signalType resetValue)
      (children signalType resetValue)) (cycleContract signalType resetValue)
      (stateCorresponds signalType resetValue) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases (children signalType resetValue .resetValue).hasCorrespondingState
      (structuralState .resetValue) with ⟨constantState, constantCorresponds⟩
  have constantState_eq : constantState = SignalMap.emptyValues := by
    funext statePort
    exact nomatch statePort
  subst constantState
  rcases (children signalType resetValue .selection).hasCorrespondingState
      (structuralState .selection) with ⟨selectionState, selectionCorresponds⟩
  have selectionState_eq : selectionState = SignalMap.emptyValues := by
    funext statePort
    exact nomatch statePort
  subst selectionState
  have constantMatches := Contracts.Cycle.Certification.childSolutionMatchesContract
    (children signalType resetValue) inputs structuralState proposal satisfies
      .resetValue SignalMap.emptyValues constantCorresponds
  have selectionMatches := Contracts.Cycle.Certification.childSolutionMatchesContract
    (children signalType resetValue) inputs structuralState proposal satisfies
      .selection SignalMap.emptyValues selectionCorresponds
  have storageMatches := Contracts.Cycle.Certification.childSolutionMatchesContract
    (children signalType resetValue) inputs structuralState proposal satisfies
      .storage contractState corresponds
  rcases constantMatches with ⟨constantEvaluates, _⟩
  rcases selectionMatches with ⟨selectionEvaluates, _⟩
  rcases storageMatches with ⟨storageEvaluates, storageNextCorresponds⟩
  rcases proposal with ⟨outputs, childProposals⟩
  let nextState := (children signalType resetValue .storage).cycleContract.stateRule.apply
    (ProposedValues.childInputs (body signalType resetValue)
      (childStructure signalType resetValue) inputs childProposals .storage) contractState
  refine ⟨nextState, ?_, storageNextCorresponds⟩
  constructor
  · intro name
    cases name
    change (outputRule signalType).Holds inputs contractState _
    rw [outputRule_holds_iff]
    exact (satisfies.1 .value).trans
      ((Register.outputRule_holds_iff signalType _ _ _).mp
        (storageEvaluates.1 Primitives.RegisterRule.observe))
  · have selected := (Mux.selectRule_holds_iff signalType _ _ _).mp
      (selectionEvaluates.1 Mux.Rule.select)
    have constantValue := (Constant.outputRule_holds_iff signalType resetValue _ _ _).mp
      (constantEvaluates.1 Primitives.ConstantRule.apply)
    have storageNextValue : nextState .stored =
        (ProposedValues.childInputs (body signalType resetValue)
          (childStructure signalType resetValue) inputs childProposals .storage) .input := by
      rfl
    change (childProposals .selection).outputs .result =
      bif inputs .reset then
        (childProposals .resetValue).outputs .output else inputs .value at selected
    funext statePort
    cases statePort
    rw [storageNextValue]
    change (childProposals .selection).outputs .result =
      bif inputs .reset then resetValue else inputs .value
    rw [selected, constantValue]

private noncomputable def proofCertification (signalType : SignalType)
    (resetValue : signalType.Denote) :
    Contracts.Cycle.ModuleCycleCertification
      (Contracts.Cycle.Certification.moduleStructure (body signalType resetValue)
        (children signalType resetValue))
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
    Contracts.Cycle.ModuleCycleCertification (moduleStructure signalType resetValue)
      (cycleContract signalType resetValue) :=
  (proofCertification signalType resetValue).transportStructure
    (moduleStructure_eq signalType resetValue).symm

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

end Silean.Modules.ResetRegister

namespace Silean.Modules.ResetRegister.Naming

open Silean Silean.Naming

def portsWithNaming (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) :
    ModulePortsNaming (Modules.ResetRegister.ports signalType) where
  inputs := ⟨fun | .value => "value" | .reset => "reset"⟩
  outputs := ⟨fun | .value => "value_out"⟩
  inputTypes := fun | .value => typeNaming | .reset => .bit
  outputTypes := fun | .value => typeNaming

def ports (signalType : SignalType) :
    ModulePortsNaming (Modules.ResetRegister.ports signalType) :=
  portsWithNaming signalType (.positional signalType)

def namingWith (signalType : SignalType) (resetValue : signalType.Denote)
    (typeNaming : SignalTypeNaming signalType) :
    ModuleNaming (Modules.ResetRegister.moduleStructure signalType resetValue) := by
  unfold Modules.ResetRegister.moduleStructure
  exact .composite
    ⟨"reset_register", "structural",
      .shape signalType :: Modules.Constant.Naming.parameters signalType resetValue⟩
    (portsWithNaming signalType typeNaming)
    (fun | .resetValue => "reset_value" | .selection => "selection" | .storage => "storage")
    (fun
      | .resetValue => Modules.Constant.Naming.namingWith signalType resetValue typeNaming
      | .selection => Modules.Mux.Naming.namingWith signalType typeNaming
      | .storage => Modules.Register.Naming.namingWith signalType typeNaming)

def naming (signalType : SignalType) (resetValue : signalType.Denote) :
    ModuleNaming (Modules.ResetRegister.moduleStructure signalType resetValue) :=
  namingWith signalType resetValue (.positional signalType)

end Silean.Modules.ResetRegister.Naming
