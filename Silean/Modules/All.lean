import Silean.Naming.ReductionNaming
import Silean.Naming.PrimitiveNaming
import Silean.Primitives.And
import Silean.Primitives.Constant

namespace Silean.Modules.All

open Silean

/-! A combinational reduction which outputs true exactly when every input bit
is true. The hardware is a balanced tree of AND gates. -/

/-! ## Lean behavior and generic reduction ingredients -/

@[reducible] private def andOperation : SignalType.bit.Denote → SignalType.bit.Denote →
    SignalType.bit.Denote := fun left right => left && right

@[reducible] private def trueValue : SignalType.bit.Denote := true

private theorem and_eq_true_iff (left right : SignalType.bit.Denote) :
    andOperation left right = trueValue ↔
      left = trueValue ∧ right = trueValue := by
  change ((left && right) = true ↔ left = true ∧ right = true)
  cases left <;> cases right <;> simp

private theorem fold_eq_true_iff : ∀ (tree : Composition.Reduction.Tree)
    (values : Fin tree.leafCount → SignalType.bit.Denote),
    Composition.Reduction.fold andOperation trueValue tree values = trueValue ↔
      ∀ index, values index = trueValue
  | .empty, values => by
      constructor
      · intro _ index
        exact Fin.elim0 index
      · intro _
        rfl
  | .leaf, values => by
      change values ⟨0, by simp [Composition.Reduction.Tree.leafCount]⟩ = true ↔ _
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
      rw [show Composition.Reduction.fold andOperation trueValue (.node left right) values =
          (Composition.Reduction.fold andOperation trueValue left (fun index =>
            values (Fin.castAdd right.leafCount index)) &&
          Composition.Reduction.fold andOperation trueValue right (fun index =>
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

private theorem fold_eq_every (tree : Composition.Reduction.Tree)
    (values : Fin tree.leafCount → SignalType.bit.Denote) :
    Composition.Reduction.fold andOperation trueValue tree values =
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
    Contracts.Cycle.Implements (.primitive Primitives.and)
      (Composition.Reduction.binaryCycleContract .bit andOperation)
      andStateCorresponds := by
  intro inputs contractState structuralState proposal corresponds satisfies
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rcases proposal with ⟨outputs, nextState⟩
    simp only [Composition.Reduction.binaryCycleContract]
    rw [Composition.Reduction.binaryOutputRule_holds_iff]
    change outputs .output = _
    simpa [andOperation, Primitives.and] using congrFun satisfies.1 .output
  · rfl

private def andImplementation :
    Composition.Reduction.BinaryImplementation .bit andOperation where
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
    Contracts.Cycle.Implements (.primitive (Primitives.constant true))
      (Composition.Reduction.identityCycleContract .bit trueValue)
      trueStateCorresponds := by
  intro inputs contractState structuralState proposal corresponds satisfies
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rcases proposal with ⟨outputs, nextState⟩
    simp only [Composition.Reduction.identityCycleContract]
    rw [Composition.Reduction.identityOutputRule_holds_iff]
    change outputs .output = _
    simpa [trueValue, Primitives.constant] using congrFun satisfies.1 .output
  · rfl

private def trueImplementation : Composition.Reduction.IdentityImplementation .bit trueValue where
  moduleStructure := .primitive (Primitives.constant true)
  certification := {
    stateCorresponds := trueStateCorresponds
    hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
    hasStructuralResult := (Primitives.constantCertified true).hasStructuralResult
    structuralResultUnique :=
      (Primitives.constantCertified true).structuralResultUnique
    implements := trueImplements }

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
  Composition.Reduction.outputRule .bit andOperation trueValue (tree width)

@[reducible] def cycleContract (width : Nat) :
    Contracts.Cycle.ModuleCycleContract (ports width) :=
  Composition.Reduction.cycleContract .bit andOperation trueValue (tree width)

@[simp] theorem outputRule_holds_iff (width : Nat)
    (inputs : (ports width).inputs.Values) (state : emptySignalMap.Values)
    (outputs : (ports width).outputs.Values) :
    (outputRule width).Holds inputs state outputs ↔
      outputs .output = every (tree width).leafCount
        (fun index => inputs (.leaf index)) := by
  change (Composition.Reduction.outputRule .bit andOperation trueValue (tree width)).Holds
      inputs state outputs ↔ _
  rw [Composition.Reduction.outputRule_holds_iff]
  rw [fold_eq_every]

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
        rw [show (tree width).leafCount = width by
          simp [tree, Composition.Reduction.balancedTree]]
        exact index.isLt⟩
    simpa [input, internal] using allTrue internal
  · intro allTrue index
    have result := allTrue (widthIndex width index)
    rw [input_widthIndex] at result
    exact result

/-! ## Hardware structure and certification -/

def moduleStructure (width : Nat) : ModuleStructure (ports width) :=
  Composition.Reduction.moduleStructure andImplementation trueImplementation (tree width)

/-- The reduction tree implementing `All` contains no blackboxes. -/
private noncomputable def reductionImplementation (width : Nat) :=
  Composition.Reduction.certification andImplementation trueImplementation (tree width)

noncomputable def certified (width : Nat) : Contracts.Cycle.ModuleCycleCertified (ports width) :=
  Composition.Reduction.certified andImplementation trueImplementation (tree width)

@[simp] theorem certified_cycleContract (width : Nat) :
    (certified width).cycleContract = cycleContract width := rfl

end Silean.Modules.All

namespace Silean.Modules.All.Naming

open Silean Silean.Naming

def ports (width : Nat) : ModulePortsNaming (Modules.All.ports width) :=
  Composition.Reduction.Naming.ports .bit (Modules.All.tree width)

def naming (width : Nat) : ModuleNaming (Modules.All.moduleStructure width) :=
  Composition.Reduction.Naming.naming "all" Modules.All.andImplementation
    Modules.All.trueImplementation Primitive.and (Primitive.constant true)
    (Modules.All.tree width) |>.withKey ⟨"all", "bit", [.natural width]⟩

def namedModule (width : Nat) : NamedModule where
  ports := Modules.All.ports width
  moduleStructure := Modules.All.moduleStructure width
  naming := naming width

end Silean.Modules.All.Naming
