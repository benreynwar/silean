import Silean2.Foundations.PortsH

namespace Silean2.Foundations

abbrev PortTrace (ports : ModulePorts) := List (BoundaryValues ports)

def PortTrace.inputs (trace : PortTrace ports) :=
  trace.map BoundaryValues.inputs

def PortTrace.outputs (trace : PortTrace ports) :=
  trace.map BoundaryValues.outputs

abbrev TraceCond (ports : ModulePorts) := PortTrace ports → Prop

def TraceCond.PrefixClosed (traceCondition: TraceCond ports) : Prop :=
  forall traceA traceB,
    traceCondition (traceA ++ traceB) → traceCondition traceA

def TraceCond.AcceptsEmpty (traceCondition : TraceCond ports) : Prop :=
  traceCondition []

def TraceCond.AcceptsNextInput (traceCondition : TraceCond ports) : Prop :=
  ∀ trace, traceCondition trace → ∀ inputs,
    ∃ outputs, traceCondition (trace ++ [{inputs := inputs, outputs := outputs}])

def TraceCond.RespectsDepSets {ports : ModulePorts}
    (traceCondition : TraceCond ports) (deps : DepSets ports): Prop :=
  ∀ trace inputsA outputsA inputsB,
    traceCondition (trace ++ [{inputs := inputsA, outputs := outputsA}]) →
      ∃ outputsB,
        traceCondition (trace ++ [{inputs := inputsB, outputs := outputsB}]) ∧
        ∀ outputKey,
          (∀ inputKey ∈ deps.requires outputKey, inputsA inputKey = inputsB inputKey ) →
          outputsA outputKey = outputsB outputKey

abbrev SpecValid
    (traceCondition : PortTrace ports → Prop)
    (deps : DepSets ports)
    : Prop :=
  TraceCond.PrefixClosed traceCondition ∧
    TraceCond.AcceptsEmpty traceCondition ∧
    TraceCond.AcceptsNextInput traceCondition ∧
    TraceCond.RespectsDepSets traceCondition deps

structure Spec (ports : ModulePorts) where
  traceCondition : PortTrace ports → Prop
  deps : DepSets ports
  valid : SpecValid traceCondition deps

theorem Spec.prefixClosed (spec : Spec ports)
  : TraceCond.PrefixClosed spec.traceCondition := spec.valid.1
theorem Spec.acceptsEmpty (spec : Spec ports)
  : TraceCond.AcceptsEmpty spec.traceCondition := spec.valid.2.1
theorem Spec.acceptsNextInput (spec : Spec ports)
  : TraceCond.AcceptsNextInput spec.traceCondition := spec.valid.2.2.1
theorem Spec.respectsDepSets (spec : Spec ports)
  : TraceCond.RespectsDepSets spec.traceCondition spec.deps := spec.valid.2.2.2

def Spec.ofFunction {ports : ModulePorts} (f : ports.Function) : Spec ports :=
  let traceCondition := fun trace => ∀ x ∈ trace, f x.inputs = x.outputs
  let deps := DepSets.whole ports
  {
    traceCondition := traceCondition
    deps := deps
    valid := by
      have prefixClosed : TraceCond.PrefixClosed traceCondition := by
        simp [TraceCond.PrefixClosed, traceCondition]
        intro traceA traceB satisfies values valuesInTrace
        have h : values ∈ traceA ∨ values ∈ traceB := by simp [valuesInTrace]
        exact satisfies values h
      have acceptsEmpty : TraceCond.AcceptsEmpty traceCondition := by
        simp [TraceCond.AcceptsEmpty, traceCondition]
      have acceptsNextInput : TraceCond.AcceptsNextInput traceCondition := by
        simp [TraceCond.AcceptsNextInput, traceCondition]
        intro trace valueCond inputs
        exists (f inputs)
        intro value valueLocation
        cases valueLocation with
        | inl inPreviousTrace => exact valueCond value inPreviousTrace
        | inr inNewValue => simp [inNewValue]
      have respectsDepSets : TraceCond.RespectsDepSets traceCondition deps := by
        simp [TraceCond.RespectsDepSets, traceCondition]
        intro trace inputsA outputsA inputsB traceAMatches
        exists (f inputsB)
        apply And.intro
        · intro x
          intro inTraceB
          by_cases h : x ∈ trace
          · exact traceAMatches x (Or.inl h)
          · simp [h] at inTraceB
            simp [inTraceB]
        · intro outputKey requiredInputsMatch
          let finalA : BoundaryValues ports := {inputs := inputsA, outputs := outputsA}
          have h2 : f inputsA = outputsA := traceAMatches finalA (Or.inr rfl)
          have h3 : ∀ inputKey, inputsA inputKey = inputsB inputKey := by
            intro inputKey
            exact requiredInputsMatch inputKey (wholeDepSetsRequireAllInputs outputKey inputKey)
          have h4 : inputsA = inputsB := by
            funext inputKey
            exact h3 inputKey
          rw [←h4]
          simp [h2]
      exact ⟨prefixClosed, acceptsEmpty, acceptsNextInput, respectsDepSets⟩

  }

end Silean2.Foundations
