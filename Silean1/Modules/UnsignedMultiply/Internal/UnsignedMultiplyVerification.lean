import Silean.Modules.UnsignedMultiply.Internal.UnsignedMultiplyArithmetic
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules

/-! Direct structural correctness proof for full-width unsigned multiplication. -/

namespace Silean.Modules.UnsignedMultiply

open Silean
open Silean.Authoring

private abbrev wholeRules (leftWidth rightWidth : Nat) :=
  ModuleStructuralCertification.Layer.wholeChildRules
    (body leftWidth rightWidth)

private abbrev rightSplitOccurrence (leftWidth rightWidth : Nat) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body leftWidth rightWidth) (wholeRules leftWidth rightWidth) :=
  ⟨.rightSplit, .apply⟩

private abbrev rowOccurrence (leftWidth rightWidth : Nat)
    (index : Fin rightWidth) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body leftWidth rightWidth) (wholeRules leftWidth rightWidth) :=
  ⟨.row index, .apply⟩

private abbrev rowsOccurrence (leftWidth rightWidth : Nat) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body leftWidth rightWidth) (wholeRules leftWidth rightWidth) :=
  ⟨.rows, .apply⟩

private abbrev treeOccurrence (leftWidth rightWidth : Nat) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body leftWidth rightWidth) (wholeRules leftWidth rightWidth) :=
  ⟨.tree, .apply⟩

private abbrev zeroOccurrence (leftWidth rightWidth : Nat) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body leftWidth rightWidth) (wholeRules leftWidth rightWidth) :=
  ⟨.zero, .apply⟩

private abbrev addOccurrence (leftWidth rightWidth : Nat) :
    ModuleStructuralCertification.Layer.RuleOccurrence
      (body leftWidth rightWidth) (wholeRules leftWidth rightWidth) :=
  ⟨.add, .apply⟩

module_complete_schedule completeSchedule (leftWidth : Nat) (rightWidth : Nat)
    for body leftWidth rightWidth with wholeRules leftWidth rightWidth := from (
    [rightSplitOccurrence leftWidth rightWidth] ++
    (Enumeration.fin rightWidth).values.map
      (rowOccurrence leftWidth rightWidth) ++
    [rowsOccurrence leftWidth rightWidth,
      treeOccurrence leftWidth rightWidth,
      zeroOccurrence leftWidth rightWidth,
      addOccurrence leftWidth rightWidth])

private theorem childStructuralCertifications
    (leftWidth rightWidth : Nat) :
    ∀ child,
      ModuleStructuralCertification
        (structuralChildren leftWidth rightWidth child)
  | .rightSplit => (Internal.rightSplitter rightWidth).structuralCertification
  | .row index =>
      (PartialProductRow.certification leftWidth rightWidth index).structural
  | .rows =>
      (Internal.rowCombiner leftWidth rightWidth).structuralCertification
  | .tree => CarrySaveTree.structuralCertification
      (leftWidth + rightWidth) rightWidth
  | .zero => (Constant.certification .bit false).structural
  | .add => (AddWithCarry.certification (leftWidth + rightWidth)).structural

/-- Contract-independent structural certification of the complete unsigned
multiplier hierarchy. -/
theorem Internal.structuralCertification (leftWidth rightWidth : Nat) :
    ModuleStructuralCertification (moduleStructure leftWidth rightWidth) :=
  (completeSchedule leftWidth rightWidth).certifyComposite
    (structuralChildren leftWidth rightWidth)
    (ModuleStructuralCertification.Layer.wholeCertifiedChildren
      (body leftWidth rightWidth)
      (structuralChildren leftWidth rightWidth)
      (childStructuralCertifications leftWidth rightWidth))
    (fun _ => rfl)

theorem Internal.result_eq_of_realization (leftWidth rightWidth : Nat)
    {step : (moduleStructure leftWidth rightWidth).Step}
    (realizes : (moduleStructure leftWidth rightWidth).Realizes step) :
    step.outputs .result =
      resultValue leftWidth rightWidth (step.inputs .left) (step.inputs .right) := by
  rcases realizes with ⟨hierStep, satisfies, rfl⟩
  let productWidth := leftWidth + rightWidth

  have rightSplitInput : (hierStep.children .rightSplit).inputs .value =
      hierStep.inputs .right := by
    simpa only [wiring, EndpointContext.moduleInput, SignalSource.value] using
      ModuleStructure.child_input satisfies (.rightSplit) (.value)
  have rightSplitOutputs : (hierStep.children .rightSplit).outputs =
      (Internal.rightSplitter rightWidth).outputValues
        (hierStep.children .rightSplit).inputs := by
    exact ModuleStructure.splitter_outputs_of_solution
      (by simpa only [structuralChildren] using
        ModuleStructure.child_isSolution satisfies (.rightSplit))
  have rightSplitAt (index : Fin rightWidth) :
      (hierStep.children .rightSplit).outputs index =
        hierStep.inputs .right index := by
    calc
      (hierStep.children .rightSplit).outputs index =
          (Internal.rightSplitter rightWidth).outputValues
            (hierStep.children .rightSplit).inputs index :=
        congrFun rightSplitOutputs index
      _ = (hierStep.children .rightSplit).inputs .value index := rfl
      _ = hierStep.inputs .right index := congrFun rightSplitInput index

  have rowLeft (index : Fin rightWidth) :
      (hierStep.children (.row index)).inputs .multiplicand =
        hierStep.inputs .left := by
    simpa only [wiring, EndpointContext.moduleInput, SignalSource.value] using
      ModuleStructure.child_input satisfies (.row index) (.multiplicand)
  have rowSelect (index : Fin rightWidth) :
      (hierStep.children (.row index)).inputs .select =
        hierStep.inputs .right index := by
    have equation := ModuleStructure.child_input satisfies
      (.row index) (.select)
    simpa only [wiring, EndpointContext.instanceOutput, SignalSource.value,
      rightSplitAt] using equation
  have rowNat (index : Fin rightWidth) :
      BitVector.toNat productWidth
          ((hierStep.children (.row index)).outputs .result) =
        PartialProductRow.resultNat leftWidth index
          (hierStep.inputs .left) (hierStep.inputs .right index) := by
    have childRealizes := ModuleStructure.child_realizes satisfies (.row index)
    simp only [structuralChildren] at childRealizes
    obtain ⟨_, _, allowed⟩ := PartialProductRow.allowed_of_realization
      leftWidth rightWidth index childRealizes
    have equation := PartialProductRow.result_toNat_of_allowed
      leftWidth rightWidth index allowed
    simp only [HierStep.step_inputs, HierStep.step_outputs] at equation
    rw [rowLeft index, rowSelect index] at equation
    exact equation

  have rowsInput (index : Fin rightWidth) :
      (hierStep.children .rows).inputs index =
        (hierStep.children (.row index)).outputs .result := by
    simpa only [wiring, EndpointContext.instanceOutput, SignalSource.value] using
      ModuleStructure.child_input satisfies (.rows) index
  have rowsOutputs : (hierStep.children .rows).outputs =
      (Internal.rowCombiner leftWidth rightWidth).outputValues
        (hierStep.children .rows).inputs := by
    exact ModuleStructure.combiner_outputs_of_solution
      (by simpa only [structuralChildren] using
        ModuleStructure.child_isSolution satisfies (.rows))
  have rowsValue (index : Fin rightWidth) :
      (hierStep.children .rows).outputs .value index =
        (hierStep.children (.row index)).outputs .result := by
    calc
      (hierStep.children .rows).outputs .value index =
          (hierStep.children .rows).inputs index := by
        simpa only [Internal.rowCombiner,
          Composition.SignalCombiner.outputValues,
          SignalType.vectorComponents, SignalType.Denote] using
            congrFun (congrFun rowsOutputs .value) index
      _ = (hierStep.children (.row index)).outputs .result := rowsInput index

  have treeInput : (hierStep.children .tree).inputs .operands =
      (hierStep.children .rows).outputs .value := by
    simpa only [wiring, EndpointContext.instanceOutput, SignalSource.value] using
      ModuleStructure.child_input satisfies (.tree) (.operands)
  have treeRealizes := ModuleStructure.child_realizes satisfies (.tree)
  simp only [structuralChildren] at treeRealizes
  have treeAccepted := CarrySaveTree.contract_of_realization
    productWidth rightWidth treeRealizes
  have treePreserves := CarrySaveTree.preservesTotal_of_contract
    productWidth rightWidth treeAccepted

  have zeroRealizes := ModuleStructure.child_realizes satisfies (.zero)
  simp only [structuralChildren] at zeroRealizes
  obtain ⟨_, _, zeroAllowed⟩ := Constant.allowed_of_realization .bit false
    zeroRealizes
  have zeroOutput := Constant.output_of_allowed .bit false zeroAllowed
  simp only [HierStep.step_outputs] at zeroOutput

  have addLeft : (hierStep.children .add).inputs .left =
      (hierStep.children .tree).outputs .resultA := by
    simpa only [wiring, EndpointContext.instanceOutput, SignalSource.value] using
      ModuleStructure.child_input satisfies (.add) (.left)
  have addRight : (hierStep.children .add).inputs .right =
      (hierStep.children .tree).outputs .resultB := by
    simpa only [wiring, EndpointContext.instanceOutput, SignalSource.value] using
      ModuleStructure.child_input satisfies (.add) (.right)
  have addCarry : (hierStep.children .add).inputs .carryIn = false := by
    calc
      (hierStep.children .add).inputs .carryIn =
          (hierStep.children .zero).outputs .output := by
        simpa only [wiring, EndpointContext.instanceOutput,
          SignalSource.value] using
          ModuleStructure.child_input satisfies (.add) (.carryIn)
      _ = false := zeroOutput
  have addRealizes := ModuleStructure.child_realizes satisfies (.add)
  simp only [structuralChildren] at addRealizes
  obtain ⟨_, _, addAllowed⟩ := AddWithCarry.allowed_of_realization productWidth
    addRealizes
  have addResult := AddWithCarry.result_toNat_of_allowed productWidth addAllowed
  simp only [HierStep.step_inputs, HierStep.step_outputs] at addResult
  rw [addLeft, addRight, addCarry] at addResult
  simp only [AddWithCarry.totalValue, Bool.toNat_false, Nat.add_zero] at addResult

  have parentResult : hierStep.outputs .result =
      (hierStep.children .add).outputs .result := by
    simpa only [wiring, EndpointContext.instanceOutput, SignalSource.value] using
      ModuleStructure.parent_output satisfies (.result)

  have rowsTotal : CarrySaveTree.inputTotal productWidth rightWidth
        ((hierStep.children .tree).inputs .operands) =
      Internal.rowNatTotal leftWidth rightWidth
        (hierStep.inputs .left) (hierStep.inputs .right) := by
    rw [treeInput]
    unfold CarrySaveTree.inputTotal Internal.rowNatTotal
    have rowValues :
        (fun index : Fin rightWidth =>
          BitVector.toNat productWidth
            ((hierStep.children .rows).outputs .value index)) =
        (fun index : Fin rightWidth =>
          PartialProductRow.resultNat leftWidth index
            (hierStep.inputs .left) (hierStep.inputs .right index)) := by
      funext index
      rw [rowsValue index, rowNat index]
    rw [rowValues]

  have resultNat : BitVector.toNat productWidth (hierStep.outputs .result) =
      BitVector.toNat leftWidth (hierStep.inputs .left) *
        BitVector.toNat rightWidth (hierStep.inputs .right) := by
    calc
      BitVector.toNat productWidth (hierStep.outputs .result) =
          BitVector.toNat productWidth
            ((hierStep.children .add).outputs .result) := by rw [parentResult]
      _ = (BitVector.toNat productWidth
              ((hierStep.children .tree).outputs .resultA) +
            BitVector.toNat productWidth
              ((hierStep.children .tree).outputs .resultB)) %
            BitVector.cardinality productWidth := addResult
      _ = CarrySaveTree.inputTotal productWidth rightWidth
              ((hierStep.children .tree).inputs .operands) %
            BitVector.cardinality productWidth := treePreserves
      _ = Internal.rowNatTotal leftWidth rightWidth
              (hierStep.inputs .left) (hierStep.inputs .right) %
            BitVector.cardinality productWidth := by rw [rowsTotal]
      _ = (BitVector.toNat leftWidth (hierStep.inputs .left) *
              BitVector.toNat rightWidth (hierStep.inputs .right)) %
            BitVector.cardinality productWidth := by
          rw [Internal.rowNatTotal_eq_product]
      _ = BitVector.toNat leftWidth (hierStep.inputs .left) *
            BitVector.toNat rightWidth (hierStep.inputs .right) := by
          rw [Nat.mod_eq_of_lt]
          exact product_lt_cardinality leftWidth rightWidth
            (hierStep.inputs .left) (hierStep.inputs .right)

  change hierStep.outputs .result =
    resultValue leftWidth rightWidth
      (hierStep.inputs .left) (hierStep.inputs .right)
  apply BitVector.toNat_injective productWidth
  rw [toNat_resultValue]
  exact resultNat

private theorem implements (leftWidth rightWidth : Nat) :
    Contracts.Cycle.Implements
      (moduleStructure leftWidth rightWidth)
      (cycleContract leftWidth rightWidth)
      (fun _ _ => True) := by
  intro _ step _ realizes
  have result := Internal.result_eq_of_realization
    leftWidth rightWidth realizes
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [applyRule_holds_iff]
    exact result
  · rfl

/-- Complete structural and behavioral certification of the full-width
unsigned multiplier. -/
noncomputable def certification (leftWidth rightWidth : Nat) :
    Contracts.Cycle.ModuleCycleCertification
      (moduleStructure leftWidth rightWidth)
      (cycleContract leftWidth rightWidth) where
  structural := Internal.structuralCertification leftWidth rightWidth
  stateCorresponds := fun _ _ => True
  hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
  implements := implements leftWidth rightWidth

noncomputable def certified (leftWidth rightWidth : Nat) :=
  (certification leftWidth rightWidth).bundle

@[simp] theorem certified_moduleStructure (leftWidth rightWidth : Nat) :
    (certified leftWidth rightWidth).moduleStructure =
      moduleStructure leftWidth rightWidth := rfl

@[simp] theorem certified_cycleContract (leftWidth rightWidth : Nat) :
    (certified leftWidth rightWidth).cycleContract =
      cycleContract leftWidth rightWidth := rfl

module_cycle_realization_bridge allowed_of_realization
    (leftWidth : Nat) (rightWidth : Nat)
    for moduleStructure leftWidth rightWidth
    implementing cycleContract leftWidth rightWidth using certification

end Silean.Modules.UnsignedMultiply
