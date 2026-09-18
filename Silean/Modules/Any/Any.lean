import Silean.Naming.ReductionNaming
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.Or
import Silean.Primitives.Constant

namespace Silean.Modules.Any

open Silean

/-! A combinational reduction which outputs true exactly when at least one
input bit is true. The hardware is a balanced tree of OR gates. -/

/-! ## Lean behavior and generic reduction ingredients -/

@[reducible] private def orOperation : SignalType.bit.Denote → SignalType.bit.Denote →
    SignalType.bit.Denote := fun left right => left || right

@[reducible] private def falseValue : SignalType.bit.Denote := false

private theorem or_eq_false_iff (left right : SignalType.bit.Denote) :
    orOperation left right = falseValue ↔
      left = falseValue ∧ right = falseValue := by
  change ((left || right) = false ↔ left = false ∧ right = false)
  cases left <;> cases right <;> simp

private theorem fold_eq_false_iff : ∀ (tree : Composition.Reduction.Tree)
    (values : Fin tree.leafCount → SignalType.bit.Denote),
    Composition.Reduction.fold orOperation falseValue tree values = falseValue ↔
      ∀ index, values index = falseValue
  | .empty, values => by
      constructor
      · intro _ index
        exact Fin.elim0 index
      · intro _
        rfl
  | .leaf, values => by
      change values ⟨0, by simp [Composition.Reduction.Tree.leafCount]⟩ = false ↔ _
      constructor
      · intro isTrue index
        change Fin 1 at index
        have index_eq : index = ⟨0, by omega⟩ := by
          apply Fin.ext
          have bound : index.val < 1 := index.isLt
          omega
        subst index
        exact isTrue
      · intro allTrue
        exact allTrue ⟨0, by simp [Composition.Reduction.Tree.leafCount]⟩
  | .node left right, values => by
      rw [show Composition.Reduction.fold orOperation falseValue (.node left right) values =
          (Composition.Reduction.fold orOperation falseValue left (fun index =>
            values (Fin.castAdd right.leafCount index)) ||
          Composition.Reduction.fold orOperation falseValue right (fun index =>
            values (Fin.natAdd left.leafCount index))) by rfl]
      rw [or_eq_false_iff]
      constructor
      · rintro ⟨leftEquation, rightEquation⟩ index
        have leftTrue := (fold_eq_false_iff left _).mp leftEquation
        have rightTrue := (fold_eq_false_iff right _).mp rightEquation
        exact Fin.addCases leftTrue rightTrue index
      · intro allTrue
        constructor
        · apply (fold_eq_false_iff left _).mpr
          exact fun index => allTrue (Fin.castAdd right.leafCount index)
        · apply (fold_eq_false_iff right _).mpr
          exact fun index => allTrue (Fin.natAdd left.leafCount index)

def some : (width : Nat) →
    (Fin width → SignalType.bit.Denote) → SignalType.bit.Denote
  | 0, _ => falseValue
  | width + 1, values =>
      orOperation (values 0) (some width fun index => values index.succ)

@[simp] theorem some_zero (values : Fin 0 → SignalType.bit.Denote) :
    some 0 values = false := rfl

@[simp] theorem some_succ (width : Nat)
    (values : Fin (width + 1) → SignalType.bit.Denote) :
    some (width + 1) values =
      (values 0 || some width fun index => values index.succ) := rfl

theorem some_eq_false_iff : ∀ (width : Nat)
    (values : Fin width → SignalType.bit.Denote),
    some width values = falseValue ↔ ∀ index, values index = falseValue
  | 0, values => by
      constructor
      · intro _ index
        exact Fin.elim0 index
      · intro _
        rfl
  | width + 1, values => by
      simp only [some]
      rw [or_eq_false_iff, some_eq_false_iff width]
      constructor
      · rintro ⟨headTrue, tailTrue⟩ index
        exact Fin.cases headTrue tailTrue index
      · intro allTrue
        exact ⟨allTrue 0, fun index => allTrue index.succ⟩

theorem some_eq_true_iff : ∀ (width : Nat)
    (values : Fin width → SignalType.bit.Denote),
    some width values = true ↔ ∃ index, values index = true
  | width, values => by
      classical
      constructor
      · intro someTrue
        by_cases existsTrue : ∃ index, values index = true
        · exact existsTrue
        · exfalso
          have allFalse : ∀ index, values index = falseValue := by
            intro index
            exact eq_false_of_ne_true (fun isTrue => existsTrue ⟨index, isTrue⟩)
          have someFalse := (some_eq_false_iff width values).mpr allFalse
          rw [someFalse] at someTrue
          contradiction
      · rintro ⟨index, value⟩
        by_cases isTrue : some width values = true
        · exact isTrue
        · exfalso
          have someFalse : some width values = falseValue :=
            eq_false_of_ne_true isTrue
          have allFalse := (some_eq_false_iff width values).mp someFalse
          rw [allFalse index] at value
          contradiction

private theorem fold_eq_some (tree : Composition.Reduction.Tree)
    (values : Fin tree.leafCount → SignalType.bit.Denote) :
    Composition.Reduction.fold orOperation falseValue tree values =
      some tree.leafCount values := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro foldTrue
    by_cases someTrue : some tree.leafCount values = true
    · exact someTrue
    · exfalso
      have someFalse : some tree.leafCount values = falseValue :=
        eq_false_of_ne_true someTrue
      have foldFalse := (fold_eq_false_iff tree values).mpr
        ((some_eq_false_iff _ values).mp someFalse)
      rw [foldFalse] at foldTrue
      contradiction
  · intro someTrue
    by_cases foldTrue :
        Composition.Reduction.fold orOperation falseValue tree values = true
    · exact foldTrue
    · exfalso
      have foldFalse :
          Composition.Reduction.fold orOperation falseValue tree values = falseValue :=
        eq_false_of_ne_true foldTrue
      have someFalse := (some_eq_false_iff _ values).mpr
        ((fold_eq_false_iff tree values).mp foldFalse)
      rw [someFalse] at someTrue
      contradiction

private def orStateCorresponds (_ : emptySignalMap.Values)
    (_ : (ModuleStructure.primitive Primitives.or).State) : Prop := True

private theorem orImplements :
    Contracts.Cycle.ImplementsSolutions (.primitive Primitives.or)
      (Composition.Reduction.binaryCycleContract .bit orOperation)
      orStateCorresponds := by
  intro contractState hierStep corresponds satisfies
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    simp only [Composition.Reduction.binaryCycleContract]
    rw [Composition.Reduction.binaryOutputRule_holds_iff]
    change hierStep.outputs .output = _
    simpa [orOperation, Primitives.or] using congrFun satisfies.1 .output
  · rfl

private def orImplementation :
    Composition.Reduction.BinaryImplementation .bit orOperation where
  moduleStructure := .primitive Primitives.or
  certification := {
    stateCorresponds := orStateCorresponds
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
    hasStructuralResult := Primitives.orCertified.hasStructuralResult
    structuralResultUnique := Primitives.orCertified.structuralResultUnique
    implements := Contracts.Cycle.implementsSolutions_iff_implements.mp orImplements }

private def falseStateCorresponds (_ : emptySignalMap.Values)
    (_ : (ModuleStructure.primitive (Primitives.constant false)).State) : Prop := True

private theorem falseImplements :
    Contracts.Cycle.ImplementsSolutions (.primitive (Primitives.constant false))
      (Composition.Reduction.identityCycleContract .bit falseValue)
      falseStateCorresponds := by
  intro contractState hierStep corresponds satisfies
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    simp only [Composition.Reduction.identityCycleContract]
    rw [Composition.Reduction.identityOutputRule_holds_iff]
    change hierStep.outputs .output = _
    simpa [falseValue, Primitives.constant] using congrFun satisfies.1 .output
  · rfl

private def falseImplementation : Composition.Reduction.IdentityImplementation .bit falseValue where
  moduleStructure := .primitive (Primitives.constant false)
  certification := {
    stateCorresponds := falseStateCorresponds
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
    hasStructuralResult := (Primitives.constantCertified false).hasStructuralResult
    structuralResultUnique :=
      (Primitives.constantCertified false).structuralResultUnique
    implements := Contracts.Cycle.implementsSolutions_iff_implements.mp falseImplements }

private abbrev tree (width : Nat) : Composition.Reduction.Tree :=
  Composition.Reduction.balancedTree width

@[reducible] def ports (width : Nat) : ModulePorts :=
  Composition.Reduction.balancedPorts .bit width

def input (width : Nat) (index : Fin width) : (ports width).inputs.Label :=
  .leaf ⟨index.val, by
    exact lt_of_lt_of_eq index.isLt (by
      simp [Composition.Reduction.balancedTree])⟩

def inputIndex (width : Nat) : (ports width).inputs.Label → Fin width
  | .leaf index => ⟨index.val, by
      simpa [Composition.Reduction.balancedTree] using index.isLt⟩

@[simp] theorem inputIndex_input (width : Nat) (index : Fin width) :
    inputIndex width (input width index) = index := by
  apply Fin.ext
  rfl

private def widthIndex (width : Nat)
    (index : Fin (tree width).leafCount) : Fin width :=
  ⟨index.val, by simpa [tree, Composition.Reduction.balancedTree] using index.isLt⟩

@[simp] private theorem input_widthIndex (width : Nat)
    (index : Fin (tree width).leafCount) :
    input width (widthIndex width index) = .leaf index := by
  apply congrArg Composition.Reduction.Input.leaf
  apply Fin.ext
  rfl

abbrev Rule := Composition.Reduction.Rule

namespace Rule

abbrev apply : Rule := Composition.Reduction.Rule.apply

end Rule

def outputRule (width : Nat) :=
  Composition.Reduction.outputRule .bit orOperation falseValue (tree width)

@[reducible] def cycleContract (width : Nat) :
    Contracts.Cycle.ModuleCycleContract (ports width) :=
  Composition.Reduction.cycleContract .bit orOperation falseValue (tree width)

@[simp] theorem outputRule_holds_iff (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values) :
    (outputRule width).Holds inputs state outputs ↔
      outputs .output = some (tree width).leafCount
        (fun index => inputs (.leaf index)) := by
  change (Composition.Reduction.outputRule .bit orOperation falseValue (tree width)).Holds
      inputs state outputs ↔ _
  rw [Composition.Reduction.outputRule_holds_iff]
  rw [fold_eq_some]

/-- The public-width form of `outputRule_holds_iff`. This avoids exposing the
internal balanced tree's leaf-index type to clients of `Any`. -/
theorem outputRule_holds_iff_width (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values) :
    (outputRule width).Holds inputs state outputs ↔
      outputs .output = some width (fun index => inputs (input width index)) := by
  rw [outputRule_holds_iff]
  have reduced : some (tree width).leafCount
      (fun index => inputs (.leaf index)) =
      some width (fun index => inputs (input width index)) := by
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro isTrue
      rcases (some_eq_true_iff _ _).mp isTrue with ⟨index, value⟩
      apply (some_eq_true_iff _ _).mpr
      exact ⟨widthIndex width index, by rw [input_widthIndex]; exact value⟩
    · intro isTrue
      rcases (some_eq_true_iff _ _).mp isTrue with ⟨index, value⟩
      let internal : Fin (tree width).leafCount :=
        ⟨index.val, by simp [tree, Composition.Reduction.balancedTree, index.isLt]⟩
      apply (some_eq_true_iff _ _).mpr
      exact ⟨internal, by simpa [input, internal] using value⟩
  rw [reduced]

theorem output_eq_true_iff_of_holds (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values)
    (holds : (outputRule width).Holds inputs state outputs) :
    outputs .output = true ↔
      ∃ index : Fin width, inputs (input width index) = true := by
  rw [(outputRule_holds_iff width inputs state outputs).mp holds]
  change some (tree width).leafCount
      (fun index => inputs (.leaf index)) = true ↔
    ∃ index : Fin width, inputs (input width index) = true
  rw [some_eq_true_iff]
  constructor
  · rintro ⟨index, value⟩
    exact ⟨widthIndex width index, by rw [input_widthIndex]; exact value⟩
  · rintro ⟨index, value⟩
    let internal : Fin (tree width).leafCount :=
      ⟨index.val, by exact lt_of_lt_of_eq index.isLt (by
        simp [Composition.Reduction.balancedTree])⟩
    exact ⟨internal, by simpa [input, internal] using value⟩

/-! ## Hardware structure and certification -/

def moduleStructure (width : Nat) : ModuleStructure (ports width) :=
  Composition.Reduction.moduleStructure orImplementation falseImplementation (tree width)

noncomputable def certification (width : Nat) :
    Contracts.Cycle.ModuleCycleCertification
      (moduleStructure width) (cycleContract width) :=
  Composition.Reduction.certification orImplementation falseImplementation (tree width)

noncomputable def certified (width : Nat) : Contracts.Cycle.ModuleCycleCertified (ports width) :=
  (certification width).bundle

@[simp] theorem certified_cycleContract (width : Nat) :
    (certified width).cycleContract = cycleContract width := rfl

end Silean.Modules.Any

namespace Silean.Modules.Any.Naming

open Silean Silean.Naming

def ports (width : Nat) : ModulePortsNaming (Modules.Any.ports width) :=
  Composition.Reduction.Naming.ports .bit (Modules.Any.tree width)

def naming (width : Nat) : ModuleNaming (Modules.Any.moduleStructure width) :=
  Composition.Reduction.Naming.naming "any" Modules.Any.orImplementation
    Modules.Any.falseImplementation Primitive.or (Primitive.constant false)
    (Modules.Any.tree width) |>.withKey ⟨"any", "bit", [.natural width]⟩

end Silean.Modules.Any.Naming

namespace Silean.Modules.Any

@[reducible] def design (width : Nat) : Silean.Naming.NamedModule where
  ports := ports width
  moduleStructure := moduleStructure width
  naming := Naming.naming width

end Silean.Modules.Any
