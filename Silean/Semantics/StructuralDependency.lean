import Silean.Semantics.StructuralEquations

namespace Silean

/-! # Structural dependencies and complete uniqueness

`StructuralRuleSpec` is boundary-only dependency information: which inputs a
rule reads and which outputs it makes available. `ModuleStructuralRules`
collects a finite, exactly covering set of those specifications independently
of any implementation or behavioral contract.

`StructuralRule` is the corresponding proof-bearing fact for one concrete
`ModuleStructure`. These rules are semantic dependencies, not evaluation
steps stored in the structure. -/

def InputsAgreeOn {ports : ModulePorts} (reads : List ports.inputs.Label)
    (left right : ports.inputs.Values) : Prop :=
  ∀ input, input ∈ reads → left input = right input

/-- Boundary-only dependency declaration for one independently schedulable
group of outputs. -/
structure StructuralRuleSpec (ports : ModulePorts) where
  /-- Boundary inputs on which the selected outputs may depend. -/
  reads : List ports.inputs.Label
  /-- Boundary outputs made available by the rule. -/
  writes : List ports.outputs.Label

/-- A finite collection of boundary structural rules. Exact output coverage
matches the invariant used by the scheduler: every output has one canonical
producing rule. -/
structure ModuleStructuralRules (ports : ModulePorts) where
  RuleName : Type
  ruleNames : Enumeration RuleName
  rule : RuleName → StructuralRuleSpec ports
  outputCoverage :
    (ruleNames.values.flatMap fun name => (rule name).writes).Perm
      ports.outputs.labels.values

namespace ModuleStructuralRules

def writtenOutputs (rules : ModuleStructuralRules ports) :
    List ports.outputs.Label :=
  rules.ruleNames.values.flatMap fun name => (rules.rule name).writes

theorem writtenOutputs_perm (rules : ModuleStructuralRules ports) :
    rules.writtenOutputs.Perm ports.outputs.labels.values :=
  rules.outputCoverage

theorem writtenOutputs_nodup (rules : ModuleStructuralRules ports) :
    rules.writtenOutputs.Nodup :=
  rules.outputCoverage.nodup_iff.mpr ports.outputs.labels.nodup

theorem rule_writes_nodup (rules : ModuleStructuralRules ports)
    (name : rules.RuleName) : (rules.rule name).writes.Nodup := by
  apply List.Sublist.nodup
    (List.sublist_flatMap_of_mem (fun selected => (rules.rule selected).writes)
      (ListIndex.get_eq (rules.ruleNames.locate name) ▸ List.get_mem _ _))
    rules.writtenOutputs_nodup

theorem rule_eq_of_both_write (rules : ModuleStructuralRules ports)
    {left right : rules.RuleName} {output : ports.outputs.Label}
    (leftWrites : output ∈ (rules.rule left).writes)
    (rightWrites : output ∈ (rules.rule right).writes) : left = right :=
  List.eq_of_mem_of_mem_of_flatMap_nodup
    (fun name => (rules.rule name).writes) rules.writtenOutputs_nodup
    (ListIndex.get_eq (rules.ruleNames.locate left) ▸ List.get_mem _ _)
    (ListIndex.get_eq (rules.ruleNames.locate right) ▸ List.get_mem _ _)
    leftWrites rightWrites

theorem output_is_written (rules : ModuleStructuralRules ports)
    (output : ports.outputs.Label) : output ∈ rules.writtenOutputs :=
  rules.outputCoverage.mem_iff.mpr
    (ListIndex.get_eq (ports.outputs.labels.locate output) ▸ List.get_mem _ _)

end ModuleStructuralRules

structure StructuralRule {ports : ModulePorts}
    (module : ModuleStructure ports) extends StructuralRuleSpec ports where
  /-- Any two solutions with equal current state and agreement on `reads`
  agree on `writes`. -/
  determines : ∀ (left right : HierStep module),
    module.IsSolution left →
    module.IsSolution right →
    HierStep.currentState module left = HierStep.currentState module right →
    InputsAgreeOn reads left.inputs right.inputs →
    ∀ output, output ∈ writes → left.outputs output = right.outputs output

/-- Complete uniqueness compares the full hierarchy assignment, including
every internal input, output, and leaf next-state value. Root inputs and
current physical state are the fixed coordinates of the structural problem. -/
def ModuleStructure.HasAtMostOneSolution {ports : ModulePorts}
    (module : ModuleStructure ports) : Prop :=
  ∀ (left right : HierStep module),
    module.IsSolution left →
    module.IsSolution right →
    left.inputs = right.inputs →
    HierStep.currentState module left = HierStep.currentState module right →
    left = right

/-- Every root input and current-state choice has a satisfying complete
hierarchy assignment. -/
def ModuleStructure.HasSolution {ports : ModulePorts}
    (module : ModuleStructure ports) : Prop :=
  ∀ inputs currentState,
    ∃ hierStep, module.IsSolution hierStep ∧
      hierStep.inputs = inputs ∧
      HierStep.currentState module hierStep = currentState

def ModuleStructure.HasExactlyOneSolution {ports : ModulePorts}
    (module : ModuleStructure ports) : Prop :=
  module.HasSolution ∧ module.HasAtMostOneSolution

/-- Contract-independent evidence that a structural hierarchy has one
well-defined solution for every boundary input and physical state.  This is
the common foundation for every behavioral certification style: cycle,
trace, relational, or otherwise. -/
structure ModuleStructuralCertification {ports : ModulePorts}
    (moduleStructure : ModuleStructure ports) where
  /-- Every boundary input and physical state admits a structural solution. -/
  hasSolution : moduleStructure.HasSolution
  /-- Two structural solutions with the same input and state are identical. -/
  hasAtMostOneSolution : moduleStructure.HasAtMostOneSolution

/-- Evidence that one concrete hierarchy both has well-defined structural
solutions and realizes a declared boundary dependency interface. -/
structure ModuleStructuralRuleCertification {ports : ModulePorts}
    (moduleStructure : ModuleStructure ports)
    (rules : ModuleStructuralRules ports) where
  structural : ModuleStructuralCertification moduleStructure
  determines : ∀ name (left right : HierStep moduleStructure),
    moduleStructure.IsSolution left →
    moduleStructure.IsSolution right →
    HierStep.currentState moduleStructure left =
      HierStep.currentState moduleStructure right →
    InputsAgreeOn (rules.rule name).reads left.inputs right.inputs →
    ∀ output, output ∈ (rules.rule name).writes →
      left.outputs output = right.outputs output

/-- A concrete hierarchy certified against a boundary structural-rule
interface. This is the contract-independent child object used by structural
layer composition. -/
structure ModuleStructuralCertifiedStructure {ports : ModulePorts}
    (rules : ModuleStructuralRules ports) where
  moduleStructure : ModuleStructure ports
  certification : ModuleStructuralRuleCertification moduleStructure rules

namespace ModuleStructuralCertification

/-- The bundled certification implies the existing proposition-level form. -/
theorem hasExactlyOneSolution
    (certification : ModuleStructuralCertification moduleStructure) :
    moduleStructure.HasExactlyOneSolution :=
  ⟨certification.hasSolution, certification.hasAtMostOneSolution⟩

/-- Transport structural certification across an equality of hierarchies. -/
theorem transport {source target : ModuleStructure ports}
    (equal : source = target)
    (certification : ModuleStructuralCertification source) :
    ModuleStructuralCertification target := by
  cases equal
  exact certification

end ModuleStructuralCertification

namespace ModuleStructuralRuleCertification

/-- Recover the proof-bearing form of one declared boundary rule. -/
def structuralRule
    (certification : ModuleStructuralRuleCertification moduleStructure rules)
    (name : rules.RuleName) : StructuralRule moduleStructure where
  reads := (rules.rule name).reads
  writes := (rules.rule name).writes
  determines := certification.determines name

/-- Transport a complete structural-rule certification across an equality of
hierarchies. -/
theorem transport {source target : ModuleStructure ports}
    (equal : source = target)
    (certification : ModuleStructuralRuleCertification source rules) :
    ModuleStructuralRuleCertification target rules := by
  cases equal
  exact certification

end ModuleStructuralRuleCertification

namespace ModuleStructuralRules

/-- Canonical name type for the universally available whole-module rule. -/
inductive WholeRule
  | apply
deriving Enumeration

/-- Safe default dependency interface: all outputs become available after all
inputs are available. -/
@[reducible] def whole (ports : ModulePorts) : ModuleStructuralRules ports where
  RuleName := WholeRule
  ruleNames := inferInstance
  rule
    | .apply => {
        reads := ports.inputs.labels.values
        writes := ports.outputs.labels.values }
  outputCoverage := by
    rw [show (inferInstance : Enumeration WholeRule).values = [.apply] by rfl]
    simp

end ModuleStructuralRules

namespace ModuleStructuralCertification

/-- Any structurally certified module automatically supports the conservative
whole-module rule. Modules may additionally certify finer dependency rules. -/
theorem wholeRuleCertification
    {ports : ModulePorts} {moduleStructure : ModuleStructure ports}
    (certification : ModuleStructuralCertification moduleStructure) :
    ModuleStructuralRuleCertification moduleStructure
      (ModuleStructuralRules.whole ports) where
  structural := certification
  determines := by
    intro name left right leftSatisfies rightSatisfies statesEqual
      inputsAgree output outputMem
    cases name
    have inputsEqual : left.inputs = right.inputs := by
      funext input
      exact inputsAgree input
        (ListIndex.get_eq (ports.inputs.labels.locate input) ▸ List.get_mem _ _)
    have stepsEqual := certification.hasAtMostOneSolution left right
      leftSatisfies rightSatisfies inputsEqual statesEqual
    exact congrFun (congrArg HierStep.outputs stepsEqual) output

/-- Package a hierarchy with its automatic whole-module rule interface. -/
def wholeCertifiedStructure
    {ports : ModulePorts} {moduleStructure : ModuleStructure ports}
    (certification : ModuleStructuralCertification moduleStructure) :
    ModuleStructuralCertifiedStructure (ModuleStructuralRules.whole ports) where
  moduleStructure := moduleStructure
  certification := certification.wholeRuleCertification

end ModuleStructuralCertification

def Primitive.ruleReads (primitive : Primitive) :
    List primitive.ports.inputs.Label :=
  primitive.outputReads

def Primitive.ruleWrites (primitive : Primitive) :
    List primitive.ports.outputs.Label :=
  primitive.ports.outputs.labels.values

/-- The assignment obtained by evaluating a primitive's defining functions.
This witnesses existence without making evaluation order part of the
structural solution relation. -/
def Primitive.canonicalHierStep (primitive : Primitive)
    (inputs : primitive.ports.inputs.Values)
    (currentState : primitive.localState.Values) :
    HierStep (.primitive primitive) :=
  { inputs := inputs
    currentState := currentState
    outputs := primitive.outputValues inputs currentState
    nextState := primitive.nextStateValues inputs currentState }

@[simp] theorem Primitive.canonicalHierStep_isSolution
    (primitive : Primitive) (inputs : primitive.ports.inputs.Values)
    (currentState : primitive.localState.Values) :
    (ModuleStructure.primitive primitive).IsSolution
      (primitive.canonicalHierStep inputs currentState) :=
  ⟨rfl, rfl⟩

theorem Primitive.hasSolution (primitive : Primitive) :
    (ModuleStructure.primitive primitive).HasSolution := by
  intro inputs currentState
  exact ⟨primitive.canonicalHierStep inputs currentState, by simp, rfl, rfl⟩

def Primitive.structuralRule (primitive : Primitive) :
    StructuralRule (.primitive primitive) where
  reads := primitive.ruleReads
  writes := primitive.ruleWrites
  determines := by
    intro left right leftSatisfies rightSatisfies statesEqual
      inputsAgree output _
    have outputsEqual := primitive.outputRespectsReads
      left.inputs right.inputs left.currentState inputsAgree
    have rightOutput :
        right.outputs = primitive.outputValues right.inputs left.currentState := by
      rw [statesEqual]
      exact rightSatisfies.1
    exact congrFun
      (leftSatisfies.1.trans (outputsEqual.trans rightOutput.symm)) output

@[simp] theorem Primitive.structuralRule_writes (primitive : Primitive) :
    primitive.structuralRule.writes = primitive.ruleWrites :=
  rfl

@[simp] theorem Primitive.structuralRule_reads (primitive : Primitive) :
    primitive.structuralRule.reads = primitive.ruleReads :=
  rfl

theorem Primitive.hasAtMostOneSolution (primitive : Primitive) :
    (ModuleStructure.primitive primitive).HasAtMostOneSolution := by
  intro left right leftSatisfies rightSatisfies inputsEqual statesEqual
  cases left
  cases right
  simp_all only [ModuleStructure.IsSolution, HierStep.inputs,
    HierStep.outputs, HierStep.currentState, HierStep.nextState,
    Primitive.IsSolution, Primitive.OutputsSatisfy,
    Primitive.NextStateSatisfy]

/-- Every concrete primitive carries contract-independent structural
certification directly from its defining equations. -/
theorem Primitive.structuralCertification (primitive : Primitive) :
    ModuleStructuralCertification (.primitive primitive) where
  hasSolution := primitive.hasSolution
  hasAtMostOneSolution := primitive.hasAtMostOneSolution

def Composition.SignalSplitter.structuralRule
    (splitter : Composition.SignalSplitter) :
    StructuralRule (.splitter splitter) where
  reads := Composition.SignalComponent.inputReads splitter.ports
  writes := Composition.SignalComponent.outputWrites splitter.ports
  determines := by
    intro left right leftSatisfies rightSatisfies _ inputsAgree output _
    exact congrFun (leftSatisfies.trans
      ((congrArg splitter.outputValues
        (Composition.SignalComponent.inputs_equal_of_agree splitter.ports
          _ _ inputsAgree)).trans rightSatisfies.symm)) output

def Composition.SignalSplitter.canonicalHierStep
    (splitter : Composition.SignalSplitter)
    (inputs : splitter.ports.inputs.Values) :
    HierStep (.splitter splitter) :=
  { inputs := inputs
    outputs := splitter.outputValues inputs }

theorem Composition.SignalSplitter.hasSolution
    (splitter : Composition.SignalSplitter) :
    (ModuleStructure.splitter splitter).HasSolution := by
  intro inputs currentState
  refine ⟨splitter.canonicalHierStep inputs, rfl, rfl, ?_⟩
  change SignalMap.emptyValues = currentState
  exact Subsingleton.elim _ _

theorem Composition.SignalSplitter.hasAtMostOneSolution
    (splitter : Composition.SignalSplitter) :
    (ModuleStructure.splitter splitter).HasAtMostOneSolution := by
  intro left right leftSatisfies rightSatisfies inputsEqual _
  cases left
  cases right
  simp_all only [ModuleStructure.IsSolution, HierStep.inputs,
    HierStep.outputs, Composition.SignalSplitter.IsSolution]

/-- Contract-independent certification of a signal splitter. -/
theorem Composition.SignalSplitter.structuralCertification
    (splitter : Composition.SignalSplitter) :
    ModuleStructuralCertification (.splitter splitter) where
  hasSolution := splitter.hasSolution
  hasAtMostOneSolution := splitter.hasAtMostOneSolution

def Composition.SignalCombiner.structuralRule
    (combiner : Composition.SignalCombiner) :
    StructuralRule (.combiner combiner) where
  reads := Composition.SignalComponent.inputReads combiner.ports
  writes := Composition.SignalComponent.outputWrites combiner.ports
  determines := by
    intro left right leftSatisfies rightSatisfies _ inputsAgree output _
    exact congrFun (leftSatisfies.trans
      ((congrArg combiner.outputValues
        (Composition.SignalComponent.inputs_equal_of_agree combiner.ports
          _ _ inputsAgree)).trans rightSatisfies.symm)) output

def Composition.SignalCombiner.canonicalHierStep
    (combiner : Composition.SignalCombiner)
    (inputs : combiner.ports.inputs.Values) :
    HierStep (.combiner combiner) :=
  { inputs := inputs
    outputs := combiner.outputValues inputs }

theorem Composition.SignalCombiner.hasSolution
    (combiner : Composition.SignalCombiner) :
    (ModuleStructure.combiner combiner).HasSolution := by
  intro inputs currentState
  refine ⟨combiner.canonicalHierStep inputs, rfl, rfl, ?_⟩
  change SignalMap.emptyValues = currentState
  exact Subsingleton.elim _ _

theorem Composition.SignalCombiner.hasAtMostOneSolution
    (combiner : Composition.SignalCombiner) :
    (ModuleStructure.combiner combiner).HasAtMostOneSolution := by
  intro left right leftSatisfies rightSatisfies inputsEqual _
  cases left
  cases right
  simp_all only [ModuleStructure.IsSolution, HierStep.inputs,
    HierStep.outputs, Composition.SignalCombiner.IsSolution]

/-- Contract-independent certification of a signal combiner. -/
theorem Composition.SignalCombiner.structuralCertification
    (combiner : Composition.SignalCombiner) :
    ModuleStructuralCertification (.combiner combiner) where
  hasSolution := combiner.hasSolution
  hasAtMostOneSolution := combiner.hasAtMostOneSolution

end Silean
