import Silean.Authoring.ModuleChildCertifications
import Silean.Authoring.ModuleCycleCertification
import Silean.Authoring.ModuleRuleSchedules
import Silean.Composition.SignalAdapterImplementation
import Silean.Modules.SignedRoundShift.Internal.SignedRoundShiftStructure
import Silean.Primitives.And
import Silean.Primitives.Or

namespace Silean.Modules.SignedRoundShift

open Silean
open Silean.Authoring
open Contracts.Cycle.Certification.Layer

module_child_certifications childContracts
    (retainedWidth : Nat) (discardedWidth : Nat)
    for body retainedWidth discardedWidth where
  retained := VectorSlice.certification .bit discardedWidth retainedWidth 0,
  guardLayout := VectorLayout.certification
    (discardedWidth + retainedWidth) 1
      (Internal.guardLayout retainedWidth discardedWidth),
  guardSplit := (Internal.splitter 1).certified.certification,
  stickyLayout := VectorLayout.certification
    (discardedWidth + retainedWidth) discardedWidth
      (Internal.stickyLayout retainedWidth discardedWidth),
  stickySplit := (Internal.splitter discardedWidth).certified.certification,
  stickyAny := Any.certification discardedWidth,
  retainedLsbLayout := VectorLayout.certification
    (discardedWidth + retainedWidth) 1
      (Internal.retainedLsbLayout retainedWidth discardedWidth),
  retainedLsbSplit := (Internal.splitter 1).certified.certification,
  roundOr := Primitives.orCertified.certification,
  roundAnd := Primitives.andCertified.certification,
  increment := Increment.certification retainedWidth,
  select := Mux.certification (.vector retainedWidth .bit)

module_rule_schedules derivedRuleSchedules
    (retainedWidth : Nat) (discardedWidth : Nat)
    for body retainedWidth discardedWidth
    with childContracts retainedWidth discardedWidth
    implementing cycleContract retainedWidth discardedWidth where
  output | .apply => [
    .retained => VectorSlice.Rule.apply,
    .guardLayout => VectorLayout.Rule.apply,
    .guardSplit => Composition.SignalComponentRule.apply,
    .stickyLayout => VectorLayout.Rule.apply,
    .stickySplit => Composition.SignalComponentRule.apply,
    .stickyAny => Any.Rule.apply,
    .retainedLsbLayout => VectorLayout.Rule.apply,
    .retainedLsbSplit => Composition.SignalComponentRule.apply,
    .roundOr => Primitives.OrRule.apply,
    .roundAnd => Primitives.AndRule.apply,
    .increment => Increment.Rule.apply,
    .select => Mux.Rule.select]
  state := []

section LayerCertification

variable (retainedWidth discardedWidth : Nat)
  (layerChildren : ChildStructures
    (body retainedWidth discardedWidth)
    (childContracts retainedWidth discardedWidth))

private theorem implements :
    Contracts.Cycle.ImplementsSolutions
      (Contracts.Cycle.Certification.Layer.moduleStructure
        (body retainedWidth discardedWidth) layerChildren)
      (cycleContract retainedWidth discardedWidth) (fun _ _ => True) := by
  intro contractState hierStep corresponds satisfies
  derive_empty_state_child_matches childMatch for
    body retainedWidth discardedWidth from
      layerChildren, hierStep, satisfies
  have boundary := satisfies.1

  have retainedEquation := VectorSlice.cycleContract.result .bit
    discardedWidth retainedWidth 0 (childMatch .retained).allowed
  change hierStep.childOutputs .retained .result =
    Internal.retainedBits retainedWidth discardedWidth
      (hierStep.inputs .value) at retainedEquation

  have guardLayoutEquation := VectorLayout.cycleContract.output
    (discardedWidth + retainedWidth) 1
    (Internal.guardLayout retainedWidth discardedWidth)
    (childMatch .guardLayout).allowed
  change hierStep.childOutputs .guardLayout .output =
    VectorLayout.apply (Internal.guardLayout retainedWidth discardedWidth)
      (hierStep.inputs .value) at guardLayoutEquation
  have guardSplitEquation :=
    (Composition.SignalSplitter.outputRule_holds_iff
      (Internal.splitter 1) _ _ _).mp
        ((childMatch .guardSplit).ruleHolds
          Composition.SignalComponentRule.apply)
  change hierStep.childOutputs .guardSplit =
    hierStep.childOutputs .guardLayout .output at guardSplitEquation
  have guardEquation :
      hierStep.childOutputs .guardSplit Internal.firstBit =
        Internal.guardBit retainedWidth discardedWidth
          (hierStep.inputs .value) := by
    rw [congrFun guardSplitEquation Internal.firstBit,
      guardLayoutEquation]
    rfl

  have stickyLayoutEquation := VectorLayout.cycleContract.output
    (discardedWidth + retainedWidth) discardedWidth
    (Internal.stickyLayout retainedWidth discardedWidth)
    (childMatch .stickyLayout).allowed
  change hierStep.childOutputs .stickyLayout .output =
    VectorLayout.apply (Internal.stickyLayout retainedWidth discardedWidth)
      (hierStep.inputs .value) at stickyLayoutEquation
  have stickySplitEquation :=
    (Composition.SignalSplitter.outputRule_holds_iff
      (Internal.splitter discardedWidth) _ _ _).mp
        ((childMatch .stickySplit).ruleHolds
          Composition.SignalComponentRule.apply)
  change hierStep.childOutputs .stickySplit =
    hierStep.childOutputs .stickyLayout .output at stickySplitEquation
  have stickyAnyEquation :=
    (Any.outputRule_holds_iff_width discardedWidth _ _ _).mp
      ((childMatch .stickyAny).ruleHolds Any.Rule.apply)
  change hierStep.childOutputs .stickyAny .output =
    Any.some discardedWidth
      (fun index => hierStep.childOutputs .stickySplit index) at stickyAnyEquation
  have stickyEquation : hierStep.childOutputs .stickyAny .output =
      Internal.stickyBit retainedWidth discardedWidth
        (hierStep.inputs .value) := by
    rw [stickyAnyEquation]
    unfold Internal.stickyBit
    apply congrArg (Any.some discardedWidth)
    funext index
    rw [congrFun stickySplitEquation index, stickyLayoutEquation]

  have retainedLsbLayoutEquation := VectorLayout.cycleContract.output
    (discardedWidth + retainedWidth) 1
    (Internal.retainedLsbLayout retainedWidth discardedWidth)
    (childMatch .retainedLsbLayout).allowed
  change hierStep.childOutputs .retainedLsbLayout .output =
    VectorLayout.apply
      (Internal.retainedLsbLayout retainedWidth discardedWidth)
      (hierStep.inputs .value) at retainedLsbLayoutEquation
  have retainedLsbSplitEquation :=
    (Composition.SignalSplitter.outputRule_holds_iff
      (Internal.splitter 1) _ _ _).mp
        ((childMatch .retainedLsbSplit).ruleHolds
          Composition.SignalComponentRule.apply)
  change hierStep.childOutputs .retainedLsbSplit =
    hierStep.childOutputs .retainedLsbLayout .output at retainedLsbSplitEquation
  have retainedLsbEquation :
      hierStep.childOutputs .retainedLsbSplit Internal.firstBit =
        Internal.retainedLsbBit retainedWidth discardedWidth
          (hierStep.inputs .value) := by
    rw [congrFun retainedLsbSplitEquation Internal.firstBit,
      retainedLsbLayoutEquation]
    rfl

  have orEquation := (Primitives.orOutputRule_holds_iff _ _ _).mp
    ((childMatch .roundOr).ruleHolds Primitives.OrRule.apply)
  change hierStep.childOutputs .roundOr .output =
    (hierStep.childOutputs .stickyAny .output ||
      hierStep.childOutputs .retainedLsbSplit Internal.firstBit) at orEquation
  have andEquation := (Primitives.andOutputRule_holds_iff _ _ _).mp
    ((childMatch .roundAnd).ruleHolds Primitives.AndRule.apply)
  change hierStep.childOutputs .roundAnd .output =
    (hierStep.childOutputs .guardSplit Internal.firstBit &&
      hierStep.childOutputs .roundOr .output) at andEquation
  have incrementEquation := Increment.cycleContract.result retainedWidth
    (childMatch .increment).allowed
  change hierStep.childOutputs .increment .result =
    Increment.incrementValue retainedWidth
      (hierStep.childOutputs .retained .result) at incrementEquation
  have selectEquation := Mux.cycleContract.result
    (.vector retainedWidth .bit) (childMatch .select).allowed
  change hierStep.childOutputs .select .result =
    bif hierStep.childOutputs .roundAnd .output then
      hierStep.childOutputs .increment .result
    else hierStep.childOutputs .retained .result at selectEquation

  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [applyRule_holds_iff]
    change hierStep.outputs .result =
      resultValue retainedWidth discardedWidth (hierStep.inputs .value)
    rw [show hierStep.outputs .result =
        hierStep.childOutputs .select .result by exact boundary .result]
    rw [selectEquation, incrementEquation, retainedEquation,
      andEquation, guardEquation, orEquation, stickyEquation,
      retainedLsbEquation]
    exact Internal.circuitResult_eq_resultValue
      retainedWidth discardedWidth (hierStep.inputs .value)
  · rfl

end LayerCertification

module_cycle_certification certification
    (retainedWidth : Nat) (discardedWidth : Nat)
    for moduleStructure retainedWidth discardedWidth
    via body retainedWidth discardedWidth
    with childContracts retainedWidth discardedWidth
    implementing cycleContract retainedWidth discardedWidth where
  schedules := derivedRuleSchedules retainedWidth discardedWidth,
  structuralChildren := structuralChildren retainedWidth discardedWidth,
  certifiedChildren := certifiedChildren retainedWidth discardedWidth,
  structuresMatch := certifiedChildren_moduleStructure
    retainedWidth discardedWidth,
  stateCorresponds := fun _ _ _ => True,
  stateCoverage := fun _ _ => ⟨SignalMap.emptyValues, trivial⟩,
  implements := implements retainedWidth discardedWidth

end Silean.Modules.SignedRoundShift
