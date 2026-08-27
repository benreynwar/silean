import Silean2.Modules.Reduction
import Silean2.Naming.ModuleNaming
import Silean2.Naming.PrimitiveNaming

namespace Silean2.Modules.All

open Silean2

@[reducible] private def andOperation : SignalType.bit.Denote → SignalType.bit.Denote →
    SignalType.bit.Denote := fun left right => left && right

@[reducible] private def trueValue : SignalType.bit.Denote := true

private theorem and_eq_true_iff (left right : SignalType.bit.Denote) :
    andOperation left right = trueValue ↔
      left = trueValue ∧ right = trueValue := by
  change ((left && right) = true ↔ left = true ∧ right = true)
  cases left <;> cases right <;> simp

private theorem fold_eq_true_iff : ∀ (tree : Reduction.Tree)
    (values : Fin tree.leafCount → SignalType.bit.Denote),
    Reduction.fold andOperation trueValue tree values = trueValue ↔
      ∀ index, values index = trueValue
  | .empty, values => by
      constructor
      · intro _ index
        exact Fin.elim0 index
      · intro _
        rfl
  | .leaf, values => by
      change values ⟨0, by simp [Reduction.Tree.leafCount]⟩ = true ↔ _
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
        exact allTrue ⟨0, by simp [Reduction.Tree.leafCount]⟩
  | .node left right, values => by
      rw [show Reduction.fold andOperation trueValue (.node left right) values =
          (Reduction.fold andOperation trueValue left (fun index =>
            values (Fin.castAdd right.leafCount index)) &&
          Reduction.fold andOperation trueValue right (fun index =>
            values (Fin.natAdd left.leafCount index))) by rfl]
      rw [and_eq_true_iff]
      constructor
      · rintro ⟨leftEquation, rightEquation⟩ index
        have leftTrue := (fold_eq_true_iff left _).mp leftEquation
        have rightTrue := (fold_eq_true_iff right _).mp rightEquation
        exact Fin.addCases leftTrue rightTrue index
      · intro allTrue
        constructor
        · apply (fold_eq_true_iff left _).mpr
          exact fun index => allTrue (Fin.castAdd right.leafCount index)
        · apply (fold_eq_true_iff right _).mpr
          exact fun index => allTrue (Fin.natAdd left.leafCount index)

def every : (width : Nat) →
    (Fin width → SignalType.bit.Denote) → SignalType.bit.Denote
  | 0, _ => trueValue
  | width + 1, values =>
      andOperation (values 0) (every width fun index => values index.succ)

theorem every_eq_true_iff : ∀ (width : Nat)
    (values : Fin width → SignalType.bit.Denote),
    every width values = trueValue ↔ ∀ index, values index = trueValue
  | 0, values => by
      constructor
      · intro _ index
        exact Fin.elim0 index
      · intro _
        rfl
  | width + 1, values => by
      simp only [every]
      rw [and_eq_true_iff, every_eq_true_iff width]
      constructor
      · rintro ⟨headTrue, tailTrue⟩ index
        exact Fin.cases headTrue tailTrue index
      · intro allTrue
        exact ⟨allTrue 0, fun index => allTrue index.succ⟩

private theorem fold_eq_every (tree : Reduction.Tree)
    (values : Fin tree.leafCount → SignalType.bit.Denote) :
    Reduction.fold andOperation trueValue tree values =
      every tree.leafCount values := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro foldTrue
    exact (every_eq_true_iff _ _).mpr
      ((fold_eq_true_iff tree values).mp foldTrue)
  · intro everyTrue
    exact (fold_eq_true_iff tree values).mpr
      ((every_eq_true_iff _ _).mp everyTrue)

private def andStateCorresponds (_ : emptySignalMap.Values)
    (_ : (ModuleStructure.primitive Primitives.and).State) : Prop := True

private theorem andImplements :
    Implements (.primitive Primitives.and)
      (Reduction.binaryCycleContract .bit andOperation)
      andStateCorresponds := by
  intro inputs contractState structuralState proposal corresponds satisfies
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rcases proposal with ⟨outputs, nextState⟩
    simp only [Reduction.binaryCycleContract]
    simp only [Reduction.binaryOutputRule, CycleOutputRule.Holds,
      SignalSelection.Matches, SignalSelection.project,
      SignalSelection.prepend, SignalMap.select]
    change outputs .output = _ ∧ True
    constructor
    · simpa [andOperation, Primitives.and] using congrFun satisfies.1 .output
    · trivial
  · rfl

private def andImplementation :
    Reduction.BinaryImplementation .bit andOperation where
  moduleStructure := .primitive Primitives.and
  certification := {
    stateCorresponds := andStateCorresponds
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
    hasStructuralResult := Primitives.andCertified.hasStructuralResult
    structuralResultUnique := Primitives.andCertified.structuralResultUnique
    implements := andImplements }

private def trueStateCorresponds (_ : emptySignalMap.Values)
    (_ : (ModuleStructure.primitive (Primitives.constant true)).State) : Prop := True

private theorem trueImplements :
    Implements (.primitive (Primitives.constant true))
      (Reduction.identityCycleContract .bit trueValue)
      trueStateCorresponds := by
  intro inputs contractState structuralState proposal corresponds satisfies
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rcases proposal with ⟨outputs, nextState⟩
    simp only [Reduction.identityCycleContract]
    simp only [Reduction.identityOutputRule, CycleOutputRule.Holds,
      SignalSelection.Matches, SignalSelection.project, SignalMap.select]
    change outputs .output = _ ∧ True
    constructor
    · simpa [trueValue, Primitives.constant] using congrFun satisfies.1 .output
    · trivial
  · rfl

private def trueImplementation : Reduction.IdentityImplementation .bit trueValue where
  moduleStructure := .primitive (Primitives.constant true)
  certification := {
    stateCorresponds := trueStateCorresponds
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
    hasStructuralResult := (Primitives.constantCertified true).hasStructuralResult
    structuralResultUnique :=
      (Primitives.constantCertified true).structuralResultUnique
    implements := trueImplements }

private def tree (width : Nat) : Reduction.Tree := Reduction.Tree.balanced width

@[reducible] def ports (width : Nat) : ModulePorts :=
  Reduction.ports .bit (tree width)

def input (width : Nat) (index : Fin width) : (ports width).inputs.Label :=
  .leaf ⟨index.val, by
    rw [show (tree width).leafCount = width by simp [tree]]
    exact index.isLt⟩

def inputIndex (width : Nat) : (ports width).inputs.Label → Fin width
  | .leaf index => ⟨index.val, by
      exact lt_of_lt_of_eq index.isLt (by simp [tree])⟩

@[simp] theorem inputIndex_input (width : Nat) (index : Fin width) :
    inputIndex width (input width index) = index := by
  apply Fin.ext
  rfl

private def widthIndex (width : Nat)
    (index : Fin (tree width).leafCount) : Fin width :=
  ⟨index.val, by
    exact lt_of_lt_of_eq index.isLt (by simp [tree])⟩

@[simp] private theorem input_widthIndex (width : Nat)
    (index : Fin (tree width).leafCount) :
    input width (widthIndex width index) = .leaf index := by
  apply congrArg Reduction.Input.leaf
  apply Fin.ext
  rfl

inductive Rule | apply
deriving Enumeration

def outputRule (width : Nat) : CycleOutputRule (ports width) emptySignalMap
    { inputTypes := SignalTypes.ofList (Reduction.inputMap .bit (tree width)).types
      outputTypes := .cons .bit .nil } where
  readsInputs := (Reduction.inputMap .bit (tree width)).allSelection
  writesOutputs := (Reduction.outputMap .bit).select .output
  target := fun packed _ =>
    (every (tree width).leafCount fun index =>
      (Reduction.inputMap .bit (tree width)).unpack packed
        (Reduction.Input.leaf index), ())

@[reducible] def cycleContract (width : Nat) : ModuleCycleContract (ports width) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, outputRule width⟩
  stateRule := CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values) :
    (outputRule width).Holds inputs state outputs ↔
      outputs .output = every (tree width).leafCount
        (fun index => inputs (.leaf index)) := by
  have values_eq :
      (fun index => (Reduction.inputMap .bit (tree width)).unpack
        ((Reduction.inputMap .bit (tree width)).allSelection.project inputs)
          (Reduction.Input.leaf index)) =
      (fun index => inputs (Reduction.Input.leaf index)) := by
    funext index
    exact congrFun
      (SignalMap.unpack_project (Reduction.inputMap .bit (tree width)) inputs)
      (Reduction.Input.leaf index)
  simp only [outputRule, CycleOutputRule.Holds, SignalSelection.Matches,
    SignalMap.select]
  rw [values_eq]
  simp

theorem output_eq_true_iff_of_holds (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values)
    (holds : (outputRule width).Holds inputs state outputs) :
    outputs .output = true ↔
      ∀ index : Fin width, inputs (input width index) = true := by
  rw [(outputRule_holds_iff width inputs state outputs).mp holds]
  change every (tree width).leafCount
      (fun index => inputs (.leaf index)) = trueValue ↔
    ∀ index : Fin width, inputs (input width index) = trueValue
  rw [every_eq_true_iff]
  constructor
  · intro allTrue index
    let internal : Fin (tree width).leafCount :=
      ⟨index.val, by
        rw [show (tree width).leafCount = width by simp [tree]]
        exact index.isLt⟩
    simpa [input, internal] using allTrue internal
  · intro allTrue index
    have result := allTrue (widthIndex width index)
    rw [input_widthIndex] at result
    exact result

def moduleStructure (width : Nat) : ModuleStructure (ports width) :=
  Reduction.moduleStructure andImplementation trueImplementation (tree width)

private def reductionImplementation (width : Nat) :=
  Reduction.certification andImplementation trueImplementation (tree width)

private theorem implements (width : Nat) :
    Implements (moduleStructure width) (cycleContract width)
      (reductionImplementation width).stateCorresponds := by
  intro inputs contractState structuralState proposal corresponds satisfies
  have contractState_eq : contractState = SignalMap.emptyValues := by
    funext impossible
    exact nomatch impossible
  subst contractState
  rcases (reductionImplementation width).implements inputs SignalMap.emptyValues
      structuralState proposal corresponds satisfies with
    ⟨nextState, evaluates, nextCorresponds⟩
  have nextState_eq : nextState = SignalMap.emptyValues := by
    funext impossible
    exact nomatch impossible
  subst nextState
  refine ⟨SignalMap.emptyValues, ?_, nextCorresponds⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    have reductionEquation := evaluates.1 Reduction.Rule.apply
    rw [Reduction.outputRule_holds_iff] at reductionEquation
    exact reductionEquation.trans (fold_eq_every (tree width) _)
  · rfl

private def implementation (width : Nat) :
    ModuleCycleCertification (moduleStructure width) (cycleContract width) where
  stateCorresponds := (reductionImplementation width).stateCorresponds
  hasCorrespondingState := (reductionImplementation width).hasCorrespondingState
  hasStructuralResult := (reductionImplementation width).hasStructuralResult
  structuralResultUnique := (reductionImplementation width).structuralResultUnique
  implements := implements width

def certified (width : Nat) : ModuleCycleCertified (ports width) :=
  (implementation width).bundle

@[simp] theorem certified_cycleContract (width : Nat) :
    (certified width).cycleContract = cycleContract width := rfl

end Silean2.Modules.All

namespace Silean2.Modules.All.Naming

open Silean2 Silean2.Naming

def ports (width : Nat) : ModulePortsNaming (Modules.All.ports width) :=
  Reduction.Naming.ports .bit (Modules.All.tree width)

def naming (width : Nat) : ModuleNaming (Modules.All.moduleStructure width) :=
  Reduction.Naming.naming "all" Modules.All.andImplementation
    Modules.All.trueImplementation Primitive.and (Primitive.constant true)
    (Modules.All.tree width) |>.withKey ⟨"all", "bit", [.natural width]⟩

def namedModule (width : Nat) : NamedModule where
  ports := Modules.All.ports width
  moduleStructure := Modules.All.moduleStructure width
  naming := naming width

end Silean2.Modules.All.Naming
