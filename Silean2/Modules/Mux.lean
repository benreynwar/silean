import Silean2.CertifiedSchedule
import Silean2.Modules.Mask
import Silean2.Modules.BitwiseOr
import Silean2.Primitives.Not

namespace Silean2.Modules.Mux

open Silean2

inductive Instance
  | invertSelect
  | chooseFalse
  | chooseTrue
  | combine
deriving Enumeration

@[reducible] def instances (signalType : SignalType) : Instances :=
  EnumeratedMap.of Instance fun
    | .invertSelect => Primitives.not.ports
    | .chooseFalse | .chooseTrue => Mask.ports signalType
    | .combine => BitwiseOr.ports signalType

inductive Input
  | select
  | whenFalse
  | whenTrue
deriving Enumeration

inductive Output
  | result
deriving Enumeration

@[reducible] def inputMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of Input fun
    | .select => .bit
    | .whenFalse | .whenTrue => signalType

@[reducible] def outputMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of Output fun | .result => signalType

@[reducible] def ports (signalType : SignalType) : ModulePorts :=
  ⟨inputMap signalType, outputMap signalType⟩

@[reducible] def context (signalType : SignalType) : EndpointContext where
  ports := ports signalType
  instances := instances signalType

def wiring (signalType : SignalType) :
    Wiring (context signalType).ports (context signalType).instances where
  moduleOutput
    | .result => (context signalType).instanceOutput .combine .result
  instanceInput
    | .invertSelect, .input =>
        (context signalType).moduleInput .select
    | .chooseFalse, .value =>
        (context signalType).moduleInput .whenFalse
    | .chooseFalse, .mask =>
        (context signalType).instanceOutput .invertSelect .output
    | .chooseTrue, .value =>
        (context signalType).moduleInput .whenTrue
    | .chooseTrue, .mask =>
        (context signalType).moduleInput .select
    | .combine, .left =>
        (context signalType).instanceOutput .chooseFalse .result
    | .combine, .right =>
        (context signalType).instanceOutput .chooseTrue .result

@[reducible] def body (signalType : SignalType) : ModuleBody where
  context := context signalType
  wiring := wiring signalType

end Silean2.Modules.Mux

namespace Silean2.Modules.Mux

open Silean2

@[reducible] noncomputable def children (signalType : SignalType) :
    Certified.Children (body signalType)
  | .invertSelect => Primitives.notCertified
  | .chooseFalse | .chooseTrue => Mask.certified signalType
  | .combine => BitwiseOr.certified signalType

@[reducible] noncomputable def childStructure (signalType : SignalType) :=
  Certified.childStructure (children signalType)

@[reducible] def structuralChildren (signalType : SignalType) :
    (name : (instances signalType).Name) →
      ModuleStructure ((instances signalType).ports name)
  | .invertSelect => Primitives.notCertified.moduleStructure
  | .chooseFalse | .chooseTrue => Mask.moduleStructure signalType
  | .combine => BitwiseOr.moduleStructure signalType

def moduleStructure (signalType : SignalType) :
    ModuleStructure (Modules.Mux.ports signalType) :=
  .composite (body signalType) (structuralChildren signalType)

theorem moduleStructure_eq (signalType : SignalType) :
    moduleStructure signalType =
      Certified.moduleStructure (body signalType) (children signalType) := by
  unfold moduleStructure Certified.moduleStructure
  congr
  funext child
  cases child <;> rfl

end Silean2.Modules.Mux

namespace Silean2.Modules.Mux

open Silean2

inductive Rule
  | select
deriving Enumeration

def selectRule (signalType : SignalType) :
    CycleOutputRule (Modules.Mux.ports signalType) emptySignalMap
      { inputTypes := .cons .bit (.cons signalType (.cons signalType .nil))
        outputTypes := .cons signalType .nil } where
  readsInputs := ((Modules.Mux.inputMap signalType).select .whenTrue
    |>.prepend .whenFalse).prepend .select
  writesOutputs := (Modules.Mux.outputMap signalType).select .result
  target
    | (select, (whenFalse, (whenTrue, ()))), _ =>
        (bif select then whenTrue else whenFalse, ())

def stateRule (signalType : SignalType) :
    CycleStateRule (Modules.Mux.ports signalType) emptySignalMap :=
  CycleStateRule.empty (Modules.Mux.ports signalType)

def cycleContract (signalType : SignalType) :
    ModuleCycleContract (Modules.Mux.ports signalType) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .select => ⟨_, selectRule signalType⟩
  stateRule := stateRule signalType
  outputCoverage := by rfl

abbrev invertRule (signalType : SignalType) :
    Certified.RuleOccurrence (children signalType) :=
  ⟨.invertSelect, Primitives.NotRule.apply⟩

abbrev falseRule (signalType : SignalType) :
    Certified.RuleOccurrence (children signalType) :=
  ⟨.chooseFalse, Mask.Rule.apply⟩

abbrev trueRule (signalType : SignalType) :
    Certified.RuleOccurrence (children signalType) :=
  ⟨.chooseTrue, Mask.Rule.apply⟩

abbrev combineRule (signalType : SignalType) :
    Certified.RuleOccurrence (children signalType) :=
  ⟨.combine, BitwiseOr.Rule.apply⟩

@[simp] theorem invertRule_reads (signalType) :
    (invertRule signalType).reads = [.input] := rfl
@[simp] theorem falseRule_reads (signalType) :
    (falseRule signalType).reads = [.value, .mask] := rfl
@[simp] theorem trueRule_reads (signalType) :
    (trueRule signalType).reads = [.value, .mask] := rfl
@[simp] theorem combineRule_reads (signalType) :
    (combineRule signalType).reads = [.left, .right] := rfl
@[simp] theorem invertRule_writes (signalType) :
    (invertRule signalType).writes = [.output] := rfl
@[simp] theorem falseRule_writes (signalType) :
    (falseRule signalType).writes = [.result] := rfl
@[simp] theorem trueRule_writes (signalType) :
    (trueRule signalType).writes = [.result] := rfl
@[simp] theorem combineRule_writes (signalType) :
    (combineRule signalType).writes = [.result] := rfl

def outputSchedule (signalType : SignalType) :
    Certified.OutputSchedule (body signalType) (children signalType)
      (cycleContract signalType) .select :=
  .call (invertRule signalType)
    (by intro port member; cases port
        simp [cycleContract, selectRule, SignalSelection.prepend,
          SignalMap.select, SignalSelection.labels, Certified.sourceAvailable,
          body, wiring, context, EndpointContext.moduleInput])
    (by simp)
  (.call (falseRule signalType)
    (by intro input member
        cases input with
        | value => simp [cycleContract, selectRule, SignalSelection.prepend,
            SignalMap.select, SignalSelection.labels, Certified.sourceAvailable,
            body, wiring, context, EndpointContext.moduleInput]
        | mask => exact ⟨.apply, by simp, by simp⟩)
    (by simp)
  (.call (trueRule signalType)
    (by intro input member; cases input <;>
      simp [cycleContract, selectRule, SignalSelection.prepend,
        SignalMap.select, SignalSelection.labels, Certified.sourceAvailable,
        body, wiring, context, EndpointContext.moduleInput])
    (by simp)
  (.call (combineRule signalType)
    (by intro input member
        cases input with
        | left => exact ⟨.apply, by simp, by simp⟩
        | right => exact ⟨.apply, by simp, by simp⟩)
    (by simp)
  (.done (by
    intro output member
    cases output
    change Certified.outputAvailable
      ([combineRule signalType, trueRule signalType, falseRule signalType,
        invertRule signalType] : Certified.Availability (children signalType))
        Instance.combine .result
    exact ⟨BitwiseOr.Rule.apply, by simp, by simp⟩)))))

def stateSchedule (signalType : SignalType) :
    Certified.StateSchedule (body signalType) (children signalType) := .done trivial

def ruleSchedules (signalType : SignalType) :
    Certified.RuleSchedules (body signalType) (children signalType)
      (cycleContract signalType) where
  output | .select => outputSchedule signalType
  state := stateSchedule signalType

theorem coversChildren (signalType : SignalType) :
    (ruleSchedules signalType).CoversChildren := by
  intro child rule
  cases child with
  | invertSelect =>
    change Primitives.NotRule at rule
    cases rule
    apply Certified.RuleSchedules.Combined.add_preserves
    apply Certified.RuleSchedules.mem_combineOutputs (ruleSchedules signalType) .select
    change invertRule signalType ∈ (outputSchedule signalType).finalAvailability
    simp [outputSchedule, Certified.Schedule.finalAvailability]
  | chooseFalse =>
    change Mask.Rule at rule
    cases rule
    apply Certified.RuleSchedules.Combined.add_preserves
    apply Certified.RuleSchedules.mem_combineOutputs (ruleSchedules signalType) .select
    change falseRule signalType ∈ (outputSchedule signalType).finalAvailability
    simp [outputSchedule, Certified.Schedule.finalAvailability]
  | chooseTrue =>
    change Mask.Rule at rule
    cases rule
    apply Certified.RuleSchedules.Combined.add_preserves
    apply Certified.RuleSchedules.mem_combineOutputs (ruleSchedules signalType) .select
    change trueRule signalType ∈ (outputSchedule signalType).finalAvailability
    simp [outputSchedule, Certified.Schedule.finalAvailability]
  | combine =>
    change BitwiseOr.Rule at rule
    cases rule
    apply Certified.RuleSchedules.Combined.add_preserves
    apply Certified.RuleSchedules.mem_combineOutputs (ruleSchedules signalType) .select
    change combineRule signalType ∈ (outputSchedule signalType).finalAvailability
    simp [outputSchedule, Certified.Schedule.finalAvailability]

theorem hasAtMostOneSolution (signalType : SignalType) :
    (Certified.moduleStructure (body signalType)
      (children signalType)).HasAtMostOneSolution :=
  (ruleSchedules signalType).hasAtMostOneSolution (coversChildren signalType)

def invertInputs (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values) : Primitives.not.ports.inputs.Values
  | .input => inputs .select

noncomputable def falseInputs (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (invert : ProposedValues (children signalType .invertSelect).moduleStructure) :
    (Mask.ports signalType).inputs.Values
  | .value => inputs .whenFalse
  | .mask => invert.outputs .output

def trueInputs (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values) :
    (Mask.ports signalType).inputs.Values
  | .value => inputs .whenTrue
  | .mask => inputs .select

noncomputable def combineInputs (signalType : SignalType)
    (chooseFalse : ProposedValues (children signalType .chooseFalse).moduleStructure)
    (chooseTrue : ProposedValues (children signalType .chooseTrue).moduleStructure) :
    (BitwiseOr.ports signalType).inputs.Values
  | .left => chooseFalse.outputs .result
  | .right => chooseTrue.outputs .result

theorem hasStructuralResult (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (currentState : (Certified.moduleStructure (body signalType)
      (children signalType)).State) :
    ∃ proposal, (Certified.moduleStructure (body signalType)
      (children signalType)).IsSolution inputs currentState proposal := by
  rcases (children signalType .invertSelect).hasStructuralResult
      (invertInputs signalType inputs) (currentState .invertSelect) with
    ⟨invert, invertSatisfies⟩
  rcases (children signalType .chooseFalse).hasStructuralResult
      (falseInputs signalType inputs invert) (currentState .chooseFalse) with
    ⟨chooseFalse, falseSatisfies⟩
  rcases (children signalType .chooseTrue).hasStructuralResult
      (trueInputs signalType inputs) (currentState .chooseTrue) with
    ⟨chooseTrue, trueSatisfies⟩
  rcases (children signalType .combine).hasStructuralResult
      (combineInputs signalType chooseFalse chooseTrue) (currentState .combine) with
    ⟨combine, combineSatisfies⟩
  let childProposals : (name : Instance) →
      ProposedValues (childStructure signalType name)
    | .invertSelect => invert
    | .chooseFalse => chooseFalse
    | .chooseTrue => chooseTrue
    | .combine => combine
  let outputs : (ports signalType).outputs.Values := fun
    | .result => combine.outputs .result
  refine ⟨ProposedValues.composite outputs childProposals, ?_⟩
  constructor
  · intro output
    cases output
    rfl
  · intro child
    cases child with
    | invertSelect =>
        change (children signalType .invertSelect).moduleStructure.IsSolution
          (ProposedValues.childInputs (body signalType) (childStructure signalType) inputs childProposals
            .invertSelect) (currentState .invertSelect) invert
        rw [show ProposedValues.childInputs (body signalType) (childStructure signalType) inputs
          childProposals .invertSelect = invertInputs signalType inputs by
            funext port; cases port; rfl]
        exact invertSatisfies
    | chooseFalse =>
        change (children signalType .chooseFalse).moduleStructure.IsSolution
          (ProposedValues.childInputs (body signalType) (childStructure signalType) inputs childProposals
            .chooseFalse) (currentState .chooseFalse) chooseFalse
        rw [show ProposedValues.childInputs (body signalType) (childStructure signalType) inputs
          childProposals .chooseFalse = falseInputs signalType inputs invert by
            funext port; cases port <;> rfl]
        exact falseSatisfies
    | chooseTrue =>
        change (children signalType .chooseTrue).moduleStructure.IsSolution
          (ProposedValues.childInputs (body signalType) (childStructure signalType) inputs childProposals
            .chooseTrue) (currentState .chooseTrue) chooseTrue
        rw [show ProposedValues.childInputs (body signalType) (childStructure signalType) inputs
          childProposals .chooseTrue = trueInputs signalType inputs by
            funext port; cases port <;> rfl]
        exact trueSatisfies
    | combine =>
        change (children signalType .combine).moduleStructure.IsSolution
          (ProposedValues.childInputs (body signalType) (childStructure signalType) inputs childProposals
            .combine) (currentState .combine) combine
        rw [show ProposedValues.childInputs (body signalType) (childStructure signalType) inputs
          childProposals .combine = combineInputs signalType chooseFalse chooseTrue by
            funext port; cases port <;> rfl]
        exact combineSatisfies

private def stateCorresponds (signalType : SignalType)
    (_ : (cycleContract signalType).state.Values)
    (_ : (Certified.moduleStructure (body signalType)
      (children signalType)).State) : Prop := True

theorem selectRule_holds_iff (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (state : (cycleContract signalType).state.Values)
    (outputs : (ports signalType).outputs.Values) :
    (selectRule signalType).Holds inputs state outputs ↔
      outputs .result = bif inputs .select then inputs .whenTrue else inputs .whenFalse := by
  simp [CycleOutputRule.Holds, selectRule, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select, SignalSelection.prepend]

mutual
  private theorem muxIdentity : ∀ (signalType : SignalType)
      (whenFalse whenTrue : signalType.Denote) (select : Bool),
      signalType.bitwiseOr
          (signalType.mask whenFalse (!select))
          (signalType.mask whenTrue select) =
        bif select then whenTrue else whenFalse
    | .bit, whenFalse, whenTrue, select => by
        cases select <;> cases whenFalse <;> cases whenTrue <;> rfl
    | .vector _ element, whenFalse, whenTrue, select => by
        cases select <;>
        funext index
        · exact muxIdentity element (whenFalse index) (whenTrue index) false
        · exact muxIdentity element (whenFalse index) (whenTrue index) true
    | .tuple fields, whenFalse, whenTrue, select =>
        muxFieldsIdentity fields whenFalse whenTrue select

  private theorem muxFieldsIdentity : ∀ (fields : SignalTypes)
      (whenFalse whenTrue : fields.Denote) (select : Bool),
      fields.bitwiseOr
          (fields.mask whenFalse (!select))
          (fields.mask whenTrue select) =
        bif select then whenTrue else whenFalse
    | .nil, (), (), _ => rfl
    | .cons head tail, (falseHead, falseTail), (trueHead, trueTail), select => by
        cases select
        · apply Prod.ext
          · exact muxIdentity head falseHead trueHead false
          · exact muxFieldsIdentity tail falseTail trueTail false
        apply Prod.ext
        · exact muxIdentity head falseHead trueHead true
        · exact muxFieldsIdentity tail falseTail trueTail true
end

private theorem implements (signalType : SignalType) :
    Implements (Certified.moduleStructure (body signalType)
      (children signalType)) (cycleContract signalType)
      (stateCorresponds signalType) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have invertImplements := Certified.childImplements (children signalType)
    inputs structuralState proposal satisfies .invertSelect SignalMap.emptyValues
      (by trivial)
  have falseImplements := Certified.childImplements (children signalType)
    inputs structuralState proposal satisfies .chooseFalse SignalMap.emptyValues
      (by trivial)
  have trueImplements := Certified.childImplements (children signalType)
    inputs structuralState proposal satisfies .chooseTrue SignalMap.emptyValues
      (by trivial)
  rcases (children signalType .combine).hasCorrespondingState
      (structuralState .combine) with ⟨combineState, combineCorresponds⟩
  have combineState_eq : combineState = SignalMap.emptyValues := by
    funext statePort
    exact nomatch statePort
  subst combineState
  have combineImplements := Certified.childImplements (children signalType)
    inputs structuralState proposal satisfies .combine SignalMap.emptyValues
      combineCorresponds
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro name
    cases name
    change (selectRule signalType).Holds inputs contractState _
    rcases proposal with ⟨outputs, childProposals⟩
    rcases invertImplements with ⟨_, invertEvaluates, _⟩
    rcases falseImplements with
      ⟨_, falseEvaluates, _⟩
    have invertBit := (Primitives.notOutputRule_holds_iff _ _ _).mp
      (invertEvaluates.1 Primitives.NotRule.apply)
    have falseOutput := (Mask.outputRule_holds_iff signalType _ _ _).mp
      (falseEvaluates.1 Mask.Rule.apply)
    rcases trueImplements with
      ⟨_, trueEvaluates, _⟩
    have trueOutput := (Mask.outputRule_holds_iff signalType _ _ _).mp
      (trueEvaluates.1 Mask.Rule.apply)
    rcases combineImplements with
      ⟨_, combineEvaluates, _⟩
    have combineOutput := (BitwiseOr.outputRule_holds_iff signalType _ _ _).mp
      (combineEvaluates.1 BitwiseOr.Rule.apply)
    have boundaryResult := boundary .result
    change outputs .result = (childProposals .combine).outputs .result at boundaryResult
    change (childProposals .chooseFalse).outputs .result =
      signalType.mask (inputs .whenFalse)
        ((childProposals .invertSelect).outputs .output) at falseOutput
    change (childProposals .chooseTrue).outputs .result =
      signalType.mask (inputs .whenTrue) (inputs .select) at trueOutput
    change (childProposals .combine).outputs .result =
      signalType.bitwiseOr ((childProposals .chooseFalse).outputs .result)
        ((childProposals .chooseTrue).outputs .result) at combineOutput
    rw [selectRule_holds_iff signalType]
    change outputs .result =
      bif inputs .select then inputs .whenTrue else inputs .whenFalse
    rw [boundaryResult, combineOutput, falseOutput, trueOutput, invertBit]
    exact muxIdentity signalType _ _ _
  · simp [cycleContract, stateRule, CycleStateRule.empty]

noncomputable def proofCertification (signalType : SignalType) :
    ModuleCycleCertification
      (Certified.moduleStructure (body signalType) (children signalType))
      (cycleContract signalType) where
  stateCorresponds := stateCorresponds signalType
  hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
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

theorem hasExactlyOneSolution (signalType : SignalType)
    (inputs : (ports signalType).inputs.Values)
    (currentState : (moduleStructure signalType).State) :
    ∃ proposal, (moduleStructure signalType).IsSolution inputs currentState proposal ∧
      ∀ other, (moduleStructure signalType).IsSolution inputs currentState other →
        other = proposal :=
  (certified signalType).hasExactlyOneStructuralResult inputs currentState

end Silean2.Modules.Mux
