import Silean.Contracts.Cycle.CycleSchedule
import Silean.Naming.PrimitiveNaming
import Silean.Primitives

namespace Silean.Modules.BitMux

open Silean

/-- A one-bit combinational mux built directly from Boolean gates. -/
inductive Instance
  /-- Produces the complement of `select`. -/
  | invertSelect
  /-- Passes `whenFalse` only when `select` is low. -/
  | chooseFalse
  /-- Passes `whenTrue` only when `select` is high. -/
  | chooseTrue
  /-- Combines the mutually exclusive selected values. -/
  | combine
deriving Enumeration

@[reducible] def instancePorts : InstancePorts :=
  EnumeratedMap.of Instance fun
    | .invertSelect => Primitives.not.ports
    | .chooseFalse | .chooseTrue => Primitives.and.ports
    | .combine => Primitives.or.ports

inductive Input
  | select
  | whenFalse
  | whenTrue
deriving Enumeration

inductive Output
  | result
deriving Enumeration

@[reducible] def inputMap : SignalMap :=
  EnumeratedMap.of Input fun
    | .select | .whenFalse | .whenTrue => .bit

@[reducible] def outputMap : SignalMap :=
  EnumeratedMap.of Output fun | .result => .bit

@[reducible] def ports : ModulePorts := ⟨inputMap, outputMap⟩

@[reducible] def context : EndpointContext where
  ports := ports
  instancePorts := instancePorts

def wiring : Wiring context.ports context.instancePorts where
  moduleOutput
    -- The OR gate produces the selected result.
    | .result => context.instanceOutput .combine .output
  instanceInput
    -- Generate the low-select condition.
    | .invertSelect, .input =>
        context.moduleInput .select
    -- Select the false input when select is low.
    | .chooseFalse, .left =>
        context.moduleInput .whenFalse
    | .chooseFalse, .right =>
        context.instanceOutput .invertSelect .output
    -- Select the true input when select is high.
    | .chooseTrue, .left =>
        context.moduleInput .whenTrue
    | .chooseTrue, .right =>
        context.moduleInput .select
    -- Combine the two selected branches.
    | .combine, .left =>
        context.instanceOutput .chooseFalse .output
    | .combine, .right =>
        context.instanceOutput .chooseTrue .output

@[reducible] def body : ModuleBody where
  context := context
  wiring := wiring

end Silean.Modules.BitMux

namespace Silean.Modules.BitMux

open Silean

@[reducible] def children : Contracts.Cycle.Certification.Children body
  | .invertSelect => Primitives.notCertified
  | .chooseFalse | .chooseTrue => Primitives.andCertified
  | .combine => Primitives.orCertified

@[reducible] def childStructure := Contracts.Cycle.Certification.childStructure children

def moduleStructure : ModuleStructure Modules.BitMux.ports :=
  Contracts.Cycle.Certification.moduleStructure body children

end Silean.Modules.BitMux

namespace Silean.Modules.BitMux.Naming

open Silean Silean.Naming

def ports : ModulePortsNaming Modules.BitMux.ports where
  inputs := ⟨fun
    | .select => "select"
    | .whenFalse => "when_false"
    | .whenTrue => "when_true"⟩
  outputs := ⟨fun | .result => "result"⟩

def instanceName : Modules.BitMux.Instance → SourceName
  | .invertSelect => "invert_select"
  | .chooseFalse => "choose_false"
  | .chooseTrue => "choose_true"
  | .combine => "combine"

def childNaming : (child : Modules.BitMux.Instance) →
    ModuleNaming (Modules.BitMux.childStructure child)
  | .invertSelect => Silean.Naming.Primitive.not
  | .chooseFalse | .chooseTrue => Silean.Naming.Primitive.and
  | .combine => Silean.Naming.Primitive.or

def naming : ModuleNaming Modules.BitMux.moduleStructure := by
  unfold Modules.BitMux.moduleStructure Contracts.Cycle.Certification.moduleStructure
  exact .composite ⟨"mux", "bit_gates", []⟩ ports instanceName childNaming

end Silean.Modules.BitMux.Naming

namespace Silean.Modules.BitMux

open Silean

inductive Rule
  | select
deriving Enumeration

def selectRule : Contracts.Cycle.CycleOutputRule Modules.BitMux.ports emptySignalMap
    (.ofLists [.bit, .bit, .bit] [.bit]) where
  readsInputs := ((Modules.BitMux.inputMap.select .whenTrue).prepend .whenFalse).prepend .select
  writesOutputs := Modules.BitMux.outputMap.select .result
  target
    | (select, (whenFalse, (whenTrue, ()))), _ =>
        (bif select then whenTrue else whenFalse, ())

def stateRule : Contracts.Cycle.CycleStateRule Modules.BitMux.ports emptySignalMap :=
  Contracts.Cycle.CycleStateRule.empty Modules.BitMux.ports

def cycleContract : Contracts.Cycle.ModuleCycleContract Modules.BitMux.ports where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .select => ⟨_, selectRule⟩
  stateRule := stateRule
  outputCoverage := by rfl

abbrev invertRule : Contracts.Cycle.Certification.RuleOccurrence children :=
  ⟨.invertSelect, Primitives.NotRule.apply⟩

abbrev falseRule : Contracts.Cycle.Certification.RuleOccurrence children :=
  ⟨.chooseFalse, Primitives.AndRule.apply⟩

abbrev trueRule : Contracts.Cycle.Certification.RuleOccurrence children :=
  ⟨.chooseTrue, Primitives.AndRule.apply⟩

abbrev combineRule : Contracts.Cycle.Certification.RuleOccurrence children :=
  ⟨.combine, Primitives.OrRule.apply⟩

@[simp] theorem invertRule_reads : invertRule.reads = [.input] := rfl
@[simp] theorem falseRule_reads : falseRule.reads = [.left, .right] := rfl
@[simp] theorem trueRule_reads : trueRule.reads = [.left, .right] := rfl
@[simp] theorem combineRule_reads : combineRule.reads = [.left, .right] := rfl
@[simp] theorem invertRule_writes : invertRule.writes = [.output] := rfl
@[simp] theorem falseRule_writes : falseRule.writes = [.output] := rfl
@[simp] theorem trueRule_writes : trueRule.writes = [.output] := rfl
@[simp] theorem combineRule_writes : combineRule.writes = [.output] := rfl

def outputSchedule : Contracts.Cycle.Certification.OutputSchedule body children cycleContract .select :=
  .call invertRule
    (by intro port member; cases port
        simp [cycleContract, selectRule, SignalSelection.prepend,
          SignalMap.select, SignalSelection.labels, Contracts.Cycle.Certification.sourceAvailable,
          body, wiring, context, EndpointContext.moduleInput])
    (by simp)
  (.call falseRule
    (by intro input member
        cases input with
        | left => simp [cycleContract, selectRule, SignalSelection.prepend,
            SignalMap.select, SignalSelection.labels, Contracts.Cycle.Certification.sourceAvailable,
            body, wiring, context, EndpointContext.moduleInput]
        | right => exact ⟨.apply, by simp, by simp⟩)
    (by simp)
  (.call trueRule
    (by intro input member; cases input <;>
      simp [cycleContract, selectRule, SignalSelection.prepend,
        SignalMap.select, SignalSelection.labels, Contracts.Cycle.Certification.sourceAvailable,
        body, wiring, context, EndpointContext.moduleInput])
    (by simp)
  (.call combineRule
    (by intro input member
        cases input with
        | left => exact ⟨.apply, by simp, by simp⟩
        | right => exact ⟨.apply, by simp, by simp⟩)
    (by simp)
  (.done (by
    intro output member
    cases output
    change Contracts.Cycle.Certification.outputAvailable
      ([combineRule, trueRule, falseRule, invertRule] :
        Contracts.Cycle.Certification.Availability children) Instance.combine .output
    exact ⟨Primitives.OrRule.apply, by simp, by simp⟩)))))

def stateSchedule : Contracts.Cycle.Certification.StateSchedule body children :=
  .done (by
    intro child input member
    cases child <;>
      simp [children, Primitives.notCertified, Primitives.notCycleContract,
        Primitives.andCertified, Primitives.andCycleContract,
        Primitives.orCertified, Primitives.orCycleContract,
        Contracts.Cycle.CycleStateRule.empty, SignalSelection.labels] at member)

def ruleSchedules : Contracts.Cycle.Certification.RuleSchedules body children cycleContract where
  output | .select => outputSchedule
  state := stateSchedule

theorem coversChildren : ruleSchedules.CoversChildren := by
  intro child rule
  cases child with
  | invertSelect =>
    change Primitives.NotRule at rule
    cases rule
    apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_preserves
    apply Contracts.Cycle.Certification.RuleSchedules.mem_combineOutputs ruleSchedules .select
    change invertRule ∈ outputSchedule.finalAvailability
    simp [outputSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]
  | chooseFalse =>
    change Primitives.AndRule at rule
    cases rule
    apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_preserves
    apply Contracts.Cycle.Certification.RuleSchedules.mem_combineOutputs ruleSchedules .select
    change falseRule ∈ outputSchedule.finalAvailability
    simp [outputSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]
  | chooseTrue =>
    change Primitives.AndRule at rule
    cases rule
    apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_preserves
    apply Contracts.Cycle.Certification.RuleSchedules.mem_combineOutputs ruleSchedules .select
    change trueRule ∈ outputSchedule.finalAvailability
    simp [outputSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]
  | combine =>
    change Primitives.OrRule at rule
    cases rule
    apply Contracts.Cycle.Certification.RuleSchedules.Combined.add_preserves
    apply Contracts.Cycle.Certification.RuleSchedules.mem_combineOutputs ruleSchedules .select
    change combineRule ∈ outputSchedule.finalAvailability
    simp [outputSchedule, Contracts.Cycle.Certification.Schedule.finalAvailability]

theorem hasAtMostOneSolution : moduleStructure.HasAtMostOneSolution :=
  ruleSchedules.hasAtMostOneSolution coversChildren

def invertInputs (inputs : ports.inputs.Values) : Primitives.not.ports.inputs.Values
  | .input => inputs .select

def falseInputs (inputs : ports.inputs.Values)
    (invert : ProposedValues (children .invertSelect).moduleStructure) :
    Primitives.and.ports.inputs.Values
  | .left => inputs .whenFalse
  | .right => invert.outputs .output

def trueInputs (inputs : ports.inputs.Values) : Primitives.and.ports.inputs.Values
  | .left => inputs .whenTrue
  | .right => inputs .select

def combineInputs
    (chooseFalse : ProposedValues (children .chooseFalse).moduleStructure)
    (chooseTrue : ProposedValues (children .chooseTrue).moduleStructure) :
    Primitives.or.ports.inputs.Values
  | .left => chooseFalse.outputs .output
  | .right => chooseTrue.outputs .output

theorem hasStructuralResult (inputs : ports.inputs.Values)
    (currentState : moduleStructure.State) :
    ∃ proposal, moduleStructure.IsSolution inputs currentState proposal := by
  rcases (children .invertSelect).hasStructuralResult
      (invertInputs inputs) (currentState .invertSelect) with
    ⟨invert, invertSatisfies⟩
  rcases (children .chooseFalse).hasStructuralResult
      (falseInputs inputs invert) (currentState .chooseFalse) with
    ⟨chooseFalse, falseSatisfies⟩
  rcases (children .chooseTrue).hasStructuralResult
      (trueInputs inputs) (currentState .chooseTrue) with
    ⟨chooseTrue, trueSatisfies⟩
  rcases (children .combine).hasStructuralResult
      (combineInputs chooseFalse chooseTrue) (currentState .combine) with
    ⟨combine, combineSatisfies⟩
  let childProposals : (name : Instance) →
      ProposedValues (childStructure name)
    | .invertSelect => invert
    | .chooseFalse => chooseFalse
    | .chooseTrue => chooseTrue
    | .combine => combine
  let outputs : ports.outputs.Values := fun
    | .result => combine.outputs .output
  refine ⟨ProposedValues.composite outputs childProposals, ?_⟩
  constructor
  · intro output
    cases output
    rfl
  · intro child
    cases child with
    | invertSelect =>
        change (children .invertSelect).moduleStructure.IsSolution
          (ProposedValues.childInputs body childStructure inputs childProposals
            .invertSelect) (currentState .invertSelect) invert
        rw [show ProposedValues.childInputs body childStructure inputs
          childProposals .invertSelect = invertInputs inputs by
            funext port; cases port; rfl]
        exact invertSatisfies
    | chooseFalse =>
        change (children .chooseFalse).moduleStructure.IsSolution
          (ProposedValues.childInputs body childStructure inputs childProposals
            .chooseFalse) (currentState .chooseFalse) chooseFalse
        rw [show ProposedValues.childInputs body childStructure inputs
          childProposals .chooseFalse = falseInputs inputs invert by
            funext port; cases port <;> rfl]
        exact falseSatisfies
    | chooseTrue =>
        change (children .chooseTrue).moduleStructure.IsSolution
          (ProposedValues.childInputs body childStructure inputs childProposals
            .chooseTrue) (currentState .chooseTrue) chooseTrue
        rw [show ProposedValues.childInputs body childStructure inputs
          childProposals .chooseTrue = trueInputs inputs by
            funext port; cases port <;> rfl]
        exact trueSatisfies
    | combine =>
        change (children .combine).moduleStructure.IsSolution
          (ProposedValues.childInputs body childStructure inputs childProposals
            .combine) (currentState .combine) combine
        rw [show ProposedValues.childInputs body childStructure inputs
          childProposals .combine = combineInputs chooseFalse chooseTrue by
            funext port; cases port <;> rfl]
        exact combineSatisfies

private def stateCorresponds (_ : cycleContract.state.Values)
    (_ : moduleStructure.State) : Prop := True

theorem selectRule_holds_iff (inputs : ports.inputs.Values)
    (state : cycleContract.state.Values) (outputs : ports.outputs.Values) :
    selectRule.Holds inputs state outputs ↔
      outputs .result = bif inputs .select then inputs .whenTrue else inputs .whenFalse := by
  simp [Contracts.Cycle.CycleOutputRule.Holds, selectRule, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select, SignalSelection.prepend]

private theorem implements : Contracts.Cycle.Implements moduleStructure cycleContract stateCorresponds := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have invertImplements := Contracts.Cycle.Certification.childImplements children inputs structuralState
    proposal satisfies .invertSelect SignalMap.emptyValues (by trivial)
  have falseImplements := Contracts.Cycle.Certification.childImplements children inputs structuralState
    proposal satisfies .chooseFalse SignalMap.emptyValues (by trivial)
  have trueImplements := Contracts.Cycle.Certification.childImplements children inputs structuralState
    proposal satisfies .chooseTrue SignalMap.emptyValues (by trivial)
  have combineImplements := Contracts.Cycle.Certification.childImplements children inputs structuralState
    proposal satisfies .combine SignalMap.emptyValues (by trivial)
  have boundary := satisfies.1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro name
    cases name
    change selectRule.Holds inputs contractState _
    rcases proposal with ⟨outputs, children⟩
    rcases invertImplements with ⟨_, invertEvaluates, _⟩
    rcases falseImplements with ⟨_, falseEvaluates, _⟩
    rcases trueImplements with ⟨_, trueEvaluates, _⟩
    rcases combineImplements with ⟨_, combineEvaluates, _⟩
    have boundary' : outputs .result = (children .combine).outputs .output := by
      simpa [ProposedValues.boundaryOutputsSatisfy, body, wiring, context,
        instancePorts, EndpointContext.instanceOutput, SignalSource.value] using
          boundary Output.result
    have invertBit := (Primitives.notOutputRule_holds_iff _ _ _).mp
      (invertEvaluates.1 Primitives.NotRule.apply)
    have falseBit := (Primitives.andOutputRule_holds_iff _ _ _).mp
      (falseEvaluates.1 Primitives.AndRule.apply)
    have trueBit := (Primitives.andOutputRule_holds_iff _ _ _).mp
      (trueEvaluates.1 Primitives.AndRule.apply)
    have combineBit := (Primitives.orOutputRule_holds_iff _ _ _).mp
      (combineEvaluates.1 Primitives.OrRule.apply)
    change (children .invertSelect).outputs .output = !inputs .select at invertBit
    change (children .chooseFalse).outputs .output =
      (inputs .whenFalse && (children .invertSelect).outputs .output) at falseBit
    change (children .chooseTrue).outputs .output =
      (inputs .whenTrue && inputs .select) at trueBit
    change (children .combine).outputs .output =
      ((children .chooseFalse).outputs .output ||
        (children .chooseTrue).outputs .output) at combineBit
    rw [selectRule_holds_iff]
    simp only [ProposedValues.outputs, moduleStructure, Contracts.Cycle.Certification.moduleStructure]
    rw [boundary', combineBit, falseBit, trueBit, invertBit]
    cases inputs .select <;> cases inputs .whenFalse <;>
      cases inputs .whenTrue <;> rfl
  · simp [cycleContract, stateRule, Contracts.Cycle.CycleStateRule.empty,
      Contracts.Cycle.CycleStateRule.apply, SignalSelection.project]

noncomputable opaque certification :
    Contracts.Cycle.ModuleCycleCertification moduleStructure cycleContract := {
  stateCorresponds := stateCorresponds,
  hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩,
  hasStructuralResult := hasStructuralResult,
  structuralResultUnique := hasAtMostOneSolution,
  implements := implements }

noncomputable def certified : Contracts.Cycle.ModuleCycleCertified ports :=
  certification.bundle

theorem hasExactlyOneSolution (inputs : ports.inputs.Values)
    (currentState : moduleStructure.State) :
    ∃ proposal, moduleStructure.IsSolution inputs currentState proposal ∧
      ∀ other, moduleStructure.IsSolution inputs currentState other →
        other = proposal :=
  certified.hasExactlyOneStructuralResult inputs currentState

end Silean.Modules.BitMux
