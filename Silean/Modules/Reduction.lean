import Silean.CertifiedSchedule
import Silean.Modules.Constant

namespace Silean.Modules.Reduction

open Silean

/-! A reduction tree records hierarchy shape independently of the operation
being reduced. Keeping the leaf count as a computed property makes recursive
module construction substantially clearer than carrying arithmetic equalities
through every node. -/

inductive Tree where
  | empty
  | leaf
  | node (left right : Tree)
deriving DecidableEq, Repr

def Tree.leafCount : Tree → Nat
  | .empty => 0
  | .leaf => 1
  | .node left right => left.leafCount + right.leafCount

def Tree.IsBalanced : Tree → Prop
  | .empty | .leaf => True
  | .node left right =>
      left.IsBalanced ∧ right.IsBalanced ∧
        left.leafCount ≤ right.leafCount + 1 ∧
        right.leafCount ≤ left.leafCount + 1

private def balancedAux : (fuel width : Nat) → Tree
  | 0, _ => .empty
  | _, 0 => .empty
  | _, 1 => .leaf
  | fuel + 1, width + 2 =>
      let leftWidth := (width + 2) / 2
      .node (balancedAux fuel leftWidth)
        (balancedAux fuel (width + 2 - leftWidth))

def Tree.balanced (width : Nat) : Tree :=
  balancedAux width width

private theorem balancedAux_leafCount (fuel width : Nat)
    (enough : width ≤ fuel) : (balancedAux fuel width).leafCount = width := by
  induction fuel generalizing width with
  | zero =>
      have : width = 0 := Nat.eq_zero_of_le_zero enough
      subst width
      rfl
  | succ fuel induction =>
      cases width with
      | zero => rfl
      | succ width =>
          cases width with
          | zero => rfl
          | succ width =>
              simp only [balancedAux, Tree.leafCount]
              let total := width + 2
              let leftWidth := total / 2
              have totalPositive : 0 < total := by omega
              have leftPositive : 0 < leftWidth := by
                dsimp [leftWidth, total]
                omega
              have leftLess : leftWidth < total := by
                dsimp [leftWidth]
                exact Nat.div_lt_self totalPositive (by omega)
              have rightLess : total - leftWidth < total := by omega
              have totalLe : total ≤ fuel + 1 := by omega
              have leftLeFuel : leftWidth ≤ fuel := by omega
              have rightLeFuel : total - leftWidth ≤ fuel := by omega
              rw [induction leftWidth leftLeFuel,
                induction (total - leftWidth) rightLeFuel]
              omega

@[simp] theorem Tree.leafCount_balanced (width : Nat) :
    (Tree.balanced width).leafCount = width := by
  exact balancedAux_leafCount width width (Nat.le_refl width)

private theorem balancedAux_isBalanced (fuel width : Nat)
    (enough : width ≤ fuel) : (balancedAux fuel width).IsBalanced := by
  induction fuel generalizing width with
  | zero =>
      have : width = 0 := Nat.eq_zero_of_le_zero enough
      subst width
      trivial
  | succ fuel induction =>
      cases width with
      | zero => trivial
      | succ width =>
          cases width with
          | zero => trivial
          | succ width =>
              let total := width + 2
              let leftWidth := total / 2
              have totalPositive : 0 < total := by omega
              have leftPositive : 0 < leftWidth := by
                dsimp [leftWidth, total]
                omega
              have leftLess : leftWidth < total := by
                dsimp [leftWidth]
                exact Nat.div_lt_self totalPositive (by omega)
              have rightLess : total - leftWidth < total := by omega
              have totalLe : total ≤ fuel + 1 := by omega
              have leftLeFuel : leftWidth ≤ fuel := by omega
              have rightLeFuel : total - leftWidth ≤ fuel := by omega
              change (balancedAux fuel leftWidth).IsBalanced ∧
                (balancedAux fuel (total - leftWidth)).IsBalanced ∧ _
              refine ⟨induction leftWidth leftLeFuel,
                induction (total - leftWidth) rightLeFuel, ?_, ?_⟩
              · rw [balancedAux_leafCount fuel leftWidth leftLeFuel,
                  balancedAux_leafCount fuel (total - leftWidth) rightLeFuel]
                omega
              · rw [balancedAux_leafCount fuel leftWidth leftLeFuel,
                  balancedAux_leafCount fuel (total - leftWidth) rightLeFuel]
                dsimp [leftWidth, total]
                omega

@[simp] theorem Tree.balanced_isBalanced (width : Nat) :
    (Tree.balanced width).IsBalanced :=
  balancedAux_isBalanced width width (Nat.le_refl width)

inductive Input (tree : Tree) where
  | leaf (index : Fin tree.leafCount)

instance (tree : Tree) : Enumeration (Input tree) :=
  let indices := Enumeration.fin tree.leafCount
  { values := indices.values.map Input.leaf
    nodup := List.nodup_map_of_injective Input.leaf
      (by intro left right equal; injection equal) indices.nodup
    locate := fun
      | .leaf index => (indices.locate index).map Input.leaf }

abbrev Output := Primitives.SingleOutput

@[reducible] def inputMap (signalType : SignalType) (tree : Tree) : SignalMap :=
  EnumeratedMap.of (Input tree) fun | .leaf _ => signalType

@[reducible] def outputMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of Output fun | .output => signalType

@[reducible] def ports (signalType : SignalType) (tree : Tree) : ModulePorts :=
  ⟨inputMap signalType tree, outputMap signalType⟩

@[reducible] def binaryInputMap (signalType : SignalType) : SignalMap :=
  EnumeratedMap.of Primitives.BinaryInput fun | .left | .right => signalType

@[reducible] def binaryPorts (signalType : SignalType) : ModulePorts :=
  ⟨binaryInputMap signalType, outputMap signalType⟩

inductive Rule | apply
deriving Enumeration

def fold (operation : α → α → α) (identity : α) :
    (tree : Tree) → (Fin tree.leafCount → α) → α
  | .empty, _ => identity
  | .leaf, values => values ⟨0, by simp [Tree.leafCount]⟩
  | .node left right, values =>
      operation
        (fold operation identity left (fun index =>
          values (Fin.castAdd right.leafCount index)))
        (fold operation identity right (fun index =>
          values (Fin.natAdd left.leafCount index)))

def outputRule (signalType : SignalType)
    (operation : signalType.Denote → signalType.Denote → signalType.Denote)
    (identity : signalType.Denote) (tree : Tree) :
    CycleOutputRule (ports signalType tree) emptySignalMap
      { inputTypes := SignalTypes.ofList (inputMap signalType tree).types
        outputTypes := .cons signalType .nil } where
  readsInputs := (inputMap signalType tree).allSelection
  writesOutputs := (outputMap signalType).select .output
  target := fun packed _ =>
    (fold operation identity tree fun index =>
      (inputMap signalType tree).unpack packed (.leaf index), ())

@[reducible] def cycleContract (signalType : SignalType)
    (operation : signalType.Denote → signalType.Denote → signalType.Denote)
    (identity : signalType.Denote) (tree : Tree) :
    ModuleCycleContract (ports signalType tree) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, outputRule signalType operation identity tree⟩
  stateRule := CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (inputs : (ports signalType tree).inputs.Values)
    (state : emptySignalMap.Values) (outputs : (ports signalType tree).outputs.Values) :
    (outputRule signalType operation identity tree).Holds inputs state outputs ↔
      outputs .output = fold operation identity tree (fun index =>
        inputs (.leaf index)) := by
  have values_eq :
      (fun index => (inputMap signalType tree).unpack
        ((inputMap signalType tree).allSelection.project inputs) (.leaf index)) =
      (fun index => inputs (.leaf index)) := by
    funext index
    exact congrFun (SignalMap.unpack_project (inputMap signalType tree) inputs)
      (.leaf index)
  simp only [outputRule, CycleOutputRule.Holds, SignalSelection.Matches,
    SignalMap.select]
  rw [values_eq]
  simp

def binaryOutputRule (signalType : SignalType)
    (operation : signalType.Denote → signalType.Denote → signalType.Denote) :
    CycleOutputRule (binaryPorts signalType) emptySignalMap
      { inputTypes := .cons signalType (.cons signalType .nil)
        outputTypes := .cons signalType .nil } where
  readsInputs := ((binaryInputMap signalType).select .right).prepend .left
  writesOutputs := (outputMap signalType).select .output
  target | (left, (right, ())), _ => (operation left right, ())

@[reducible] def binaryCycleContract (signalType : SignalType)
    (operation : signalType.Denote → signalType.Denote → signalType.Denote) :
    ModuleCycleContract (binaryPorts signalType) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, binaryOutputRule signalType operation⟩
  stateRule := CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem binaryOutputRule_holds_iff
    (inputs : (binaryPorts signalType).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (binaryPorts signalType).outputs.Values) :
    (binaryOutputRule signalType operation).Holds inputs state outputs ↔
      outputs .output = operation (inputs .left) (inputs .right) := by
  simp [binaryOutputRule, CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalSelection.prepend, SignalMap.select]

structure BinaryImplementation (signalType : SignalType)
    (operation : signalType.Denote → signalType.Denote → signalType.Denote) where
  moduleStructure : ModuleStructure (binaryPorts signalType)
  certification : ModuleCycleCertification moduleStructure
    (binaryCycleContract signalType operation)

def BinaryImplementation.certified
    (implementation : BinaryImplementation signalType operation) :
    ModuleCycleCertified (binaryPorts signalType) :=
  implementation.certification.bundle

@[reducible] def identityPorts (signalType : SignalType) : ModulePorts :=
  ⟨emptySignalMap, outputMap signalType⟩

def identityOutputRule (signalType : SignalType) (identity : signalType.Denote) :
    CycleOutputRule (identityPorts signalType) emptySignalMap
      { inputTypes := .nil, outputTypes := .cons signalType .nil } where
  readsInputs := .nil
  writesOutputs := (outputMap signalType).select .output
  target | (), _ => (identity, ())

@[reducible] def identityCycleContract (signalType : SignalType)
    (identity : signalType.Denote) : ModuleCycleContract (identityPorts signalType) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => ⟨_, identityOutputRule signalType identity⟩
  stateRule := CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem identityOutputRule_holds_iff
    (inputs : (identityPorts signalType).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (identityPorts signalType).outputs.Values) :
    (identityOutputRule signalType identity).Holds inputs state outputs ↔
      outputs .output = identity := by
  simp [identityOutputRule, CycleOutputRule.Holds, SignalSelection.Matches,
    SignalSelection.project, SignalMap.select]

structure IdentityImplementation (signalType : SignalType)
    (identity : signalType.Denote) where
  moduleStructure : ModuleStructure (identityPorts signalType)
  certification : ModuleCycleCertification moduleStructure
    (identityCycleContract signalType identity)

def IdentityImplementation.certified
    (implementation : IdentityImplementation signalType identity) :
    ModuleCycleCertified (identityPorts signalType) :=
  implementation.certification.bundle

private inductive EmptyInstance | identity
deriving Enumeration

private def emptyInstances (signalType : SignalType) : Instances :=
  EnumeratedMap.of EmptyInstance fun | .identity => identityPorts signalType

private def emptyContext (signalType : SignalType) : EndpointContext where
  ports := ports signalType .empty
  instances := emptyInstances signalType

private def emptyWiring (signalType : SignalType) :
    Wiring (emptyContext signalType).ports (emptyContext signalType).instances where
  moduleOutput := fun outputName => match outputName with
    | Primitives.SingleOutput.output =>
        (emptyContext signalType).instanceOutput EmptyInstance.identity Primitives.SingleOutput.output
  instanceInput := fun child input => match child with
    | EmptyInstance.identity => nomatch input

private def emptyBody (signalType : SignalType) : ModuleBody :=
  ⟨emptyContext signalType, emptyWiring signalType⟩

private def emptyChildren
    (implementation : IdentityImplementation signalType identity) :
    Certified.Children (emptyBody signalType)
  | .identity => implementation.certified

private inductive LeafInstance

private instance : Enumeration LeafInstance :=
  Enumeration.empty fun impossible => nomatch impossible

@[reducible] private def leafInstances : Instances :=
  EnumeratedMap.of LeafInstance fun impossible => nomatch impossible

@[reducible] private def leafContext (signalType : SignalType) : EndpointContext where
  ports := ports signalType .leaf
  instances := leafInstances

@[reducible] private def leafWiring (signalType : SignalType) :
    Wiring (leafContext signalType).ports (leafContext signalType).instances where
  moduleOutput := fun outputName => match outputName with
    | Primitives.SingleOutput.output => (leafContext signalType).moduleInput
        (Input.leaf ⟨0, by simp [Tree.leafCount]⟩)
  instanceInput := fun impossible _ => nomatch impossible

@[reducible] private def leafBody (signalType : SignalType) : ModuleBody :=
  ⟨leafContext signalType, leafWiring signalType⟩

private def leafChildren : Certified.Children (leafBody signalType) :=
  fun impossible => nomatch impossible

private inductive NodeInstance | left | right | combine
deriving Enumeration

@[reducible] private def nodeInstances (signalType : SignalType) (left right : Tree) : Instances :=
  EnumeratedMap.of NodeInstance fun
    | .left => ports signalType left
    | .right => ports signalType right
    | .combine => binaryPorts signalType

@[reducible] private def nodeContext (signalType : SignalType) (left right : Tree) :
    EndpointContext where
  ports := ports signalType (.node left right)
  instances := nodeInstances signalType left right

@[reducible] private def nodeWiring (signalType : SignalType) (left right : Tree) :
    Wiring (nodeContext signalType left right).ports
      (nodeContext signalType left right).instances where
  moduleOutput := fun outputName => match outputName with
    | Primitives.SingleOutput.output => (nodeContext signalType left right).instanceOutput
        NodeInstance.combine Primitives.SingleOutput.output
  instanceInput := fun
    | NodeInstance.left, Input.leaf index =>
        (nodeContext signalType left right).moduleInput
          (Input.leaf (Fin.castAdd right.leafCount index))
    | NodeInstance.right, Input.leaf index =>
        (nodeContext signalType left right).moduleInput
          (Input.leaf (Fin.natAdd left.leafCount index))
    | NodeInstance.combine, Primitives.BinaryInput.left =>
        (nodeContext signalType left right).instanceOutput
          NodeInstance.left Primitives.SingleOutput.output
    | NodeInstance.combine, Primitives.BinaryInput.right =>
        (nodeContext signalType left right).instanceOutput
          NodeInstance.right Primitives.SingleOutput.output

@[reducible] private def nodeBody (signalType : SignalType) (left right : Tree) : ModuleBody :=
  ⟨nodeContext signalType left right, nodeWiring signalType left right⟩

def moduleStructure (binary : BinaryImplementation signalType operation)
    (identityModule : IdentityImplementation signalType identity) :
    (tree : Tree) → ModuleStructure (ports signalType tree)
  | .empty => .composite (emptyBody signalType) fun
      | .identity => identityModule.moduleStructure
  | .leaf => .composite (leafBody signalType) fun impossible => nomatch impossible
  | .node left right =>
      .composite (nodeBody signalType left right) fun
        | .left => moduleStructure binary identityModule left
        | .right => moduleStructure binary identityModule right
        | .combine => binary.moduleStructure

private abbrev Implementation (binary : BinaryImplementation signalType operation)
    (identityModule : IdentityImplementation signalType identity)
    (tree : Tree) := ModuleCycleCertification
      (moduleStructure binary identityModule tree)
      (cycleContract signalType operation identity tree)

private abbrev emptyOccurrence
    (identityModule : IdentityImplementation signalType identity) :
    Certified.RuleOccurrence (emptyChildren identityModule) :=
  ⟨EmptyInstance.identity, Rule.apply⟩

private def emptyOutputSchedule
    (identityModule : IdentityImplementation signalType identity) :
    Certified.OutputSchedule (emptyBody signalType) (emptyChildren identityModule)
      (cycleContract signalType operation identity .empty) .apply :=
  .call (emptyOccurrence identityModule)
    (by intro input member; exact nomatch input)
    (by simp)
    (.done (by
      intro outputName member
      cases outputName
      exact ⟨Rule.apply, by simp,
        by
          change Primitives.SingleOutput.output ∈
            (identityOutputRule signalType identity).writesOutputs.labels
          simp [identityOutputRule, SignalMap.select, SignalSelection.labels]⟩))

private def emptyStateSchedule
    (identityModule : IdentityImplementation signalType identity) :
    Certified.StateSchedule (emptyBody signalType) (emptyChildren identityModule) :=
  .done (by
    intro child input member
    cases child
    change input ∈ (CycleStateRule.empty (identityPorts signalType)).readsInputs.labels
      at member
    exact nomatch member)

private def emptyRuleSchedules
    (identityModule : IdentityImplementation signalType identity) :
    Certified.RuleSchedules (emptyBody signalType) (emptyChildren identityModule)
      (cycleContract signalType operation identity .empty) where
  output | .apply => emptyOutputSchedule identityModule
  state := emptyStateSchedule identityModule

private theorem emptyCoversChildren
    (identityModule : IdentityImplementation signalType identity) :
    (emptyRuleSchedules (operation := operation) identityModule).CoversChildren := by
  intro child rule
  cases child
  change Rule at rule
  cases rule
  apply Certified.RuleSchedules.Combined.add_preserves
  apply Certified.RuleSchedules.mem_combineOutputs
    (emptyRuleSchedules (operation := operation) identityModule) .apply
  simp [emptyRuleSchedules, emptyOutputSchedule,
    Certified.Schedule.finalAvailability]

private theorem emptyUnique
    {signalType : SignalType}
    {operation : signalType.Denote → signalType.Denote → signalType.Denote}
    {identity : signalType.Denote}
    {binary : BinaryImplementation signalType operation}
    (identityModule : IdentityImplementation signalType identity) :
    (moduleStructure binary identityModule .empty).HasAtMostOneSolution := by
  have structure_eq : moduleStructure binary identityModule .empty =
      Certified.moduleStructure (emptyBody signalType) (emptyChildren identityModule) := by
    apply congrArg (ModuleStructure.composite (emptyBody signalType))
    funext child
    cases child
    rfl
  rw [structure_eq]
  exact (emptyRuleSchedules (operation := operation) identityModule).hasAtMostOneSolution
    (emptyCoversChildren (operation := operation) identityModule)

private theorem emptyHasStructuralResult
    (identityModule : IdentityImplementation signalType identity)
    (inputs : (ports signalType .empty).inputs.Values)
    (state : (moduleStructure binary identityModule .empty).State) :
    ∃ proposal, (moduleStructure binary identityModule .empty).IsSolution
      inputs state proposal := by
  rcases identityModule.certification.hasStructuralResult
      (fun impossible => nomatch impossible) (state .identity) with
    ⟨identityProposal, identitySatisfies⟩
  let outputs : (ports signalType .empty).outputs.Values := fun
    | .output => identityProposal.outputs .output
  let proposal : ProposedValues (moduleStructure binary identityModule .empty) :=
    ProposedValues.composite outputs fun | .identity => identityProposal
  refine ⟨proposal, ?_⟩
  constructor
  · intro outputName
    cases outputName
    rfl
  · intro child
    cases child
    change identityModule.moduleStructure.IsSolution
      (ProposedValues.childInputs (emptyBody signalType) _ inputs proposal.2 .identity)
      (state .identity) identityProposal
    rw [show ProposedValues.childInputs (emptyBody signalType) _ inputs
        proposal.2 .identity = (fun impossible => nomatch impossible) by
      funext impossible
      exact nomatch impossible]
    exact identitySatisfies

private def emptyStateCorresponds
    (identityModule : IdentityImplementation signalType identity)
    (_ : emptySignalMap.Values)
    (state : (moduleStructure binary identityModule .empty).State) : Prop :=
  identityModule.certification.stateCorresponds SignalMap.emptyValues
    (state .identity)

private theorem emptyImplements
    (identityModule : IdentityImplementation signalType identity) :
    Implements (moduleStructure binary identityModule .empty)
      (cycleContract signalType operation identity .empty)
      (emptyStateCorresponds (binary := binary) identityModule) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, children⟩
  rcases satisfies with ⟨boundary, childSatisfies⟩
  have childInputs_eq : ProposedValues.childInputs (emptyBody signalType) _ inputs
      children .identity = (fun impossible => nomatch impossible) := by
    funext impossible
    exact nomatch impossible
  have identitySatisfies := childSatisfies .identity
  rw [childInputs_eq] at identitySatisfies
  rcases identityModule.certification.implements
      (fun impossible => nomatch impossible) SignalMap.emptyValues
      (structuralState .identity) (children .identity) corresponds identitySatisfies with
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
    have identityEquation := evaluates.1 Rule.apply
    rw [identityOutputRule_holds_iff] at identityEquation
    exact (boundary .output).trans identityEquation
  · rfl

private def emptyImplementation
    (identityModule : IdentityImplementation signalType identity) :
    Implementation binary identityModule .empty where
  stateCorresponds := emptyStateCorresponds (binary := binary) identityModule
  hasCorrespondingState := by
    intro state
    rcases identityModule.certification.hasCorrespondingState (state .identity) with
      ⟨contractState, corresponds⟩
    have contractState_eq : contractState = SignalMap.emptyValues := by
      funext impossible
      exact nomatch impossible
    subst contractState
    exact ⟨SignalMap.emptyValues, corresponds⟩
  hasStructuralResult := emptyHasStructuralResult identityModule
  structuralResultUnique := emptyUnique identityModule
  implements := emptyImplements identityModule

private def leafProposal (inputs : (ports signalType .leaf).inputs.Values) :
    ProposedValues (moduleStructure (signalType := signalType)
      binary identityModule .leaf) :=
  ProposedValues.composite
    (fun | .output => inputs (.leaf ⟨0, by simp [Tree.leafCount]⟩))
    (fun impossible => nomatch impossible)

private theorem leafProposal_satisfies
    (inputs : (ports signalType .leaf).inputs.Values)
    (state : (moduleStructure binary identityModule .leaf).State) :
    (moduleStructure (signalType := signalType) binary identityModule .leaf).IsSolution inputs state
      (leafProposal (binary := binary) (identityModule := identityModule) inputs) := by
  constructor
  · intro outputName
    cases outputName
    rfl
  · intro impossible
    exact nomatch impossible

private theorem leafUnique :
    (moduleStructure (signalType := signalType) binary identityModule .leaf).HasAtMostOneSolution := by
  intro inputs state left right leftSatisfies rightSatisfies
  rcases left with ⟨leftOutputs, leftChildren⟩
  rcases right with ⟨rightOutputs, rightChildren⟩
  have outputsEqual : leftOutputs = rightOutputs := by
    funext outputName
    exact (leftSatisfies.1 outputName).trans
      (rightSatisfies.1 outputName).symm
  have childrenEqual : leftChildren = rightChildren := by
    funext impossible
    exact nomatch impossible
  cases outputsEqual
  cases childrenEqual
  rfl

private theorem leafImplements :
    Implements (moduleStructure (signalType := signalType) binary identityModule .leaf)
      (cycleContract signalType operation identity .leaf)
      (fun (_ : emptySignalMap.Values) _ => True) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    rw [outputRule_holds_iff]
    rcases proposal with ⟨outputs, children⟩
    change outputs Primitives.SingleOutput.output = _
    simpa [fold, Tree.leafCount, leafBody, leafWiring, leafContext,
      EndpointContext.moduleInput, SignalSource.value] using
        satisfies.1 Primitives.SingleOutput.output
  · rfl

private def leafImplementation : Implementation binary identityModule .leaf where
  stateCorresponds := fun _ _ => True
  hasCorrespondingState := fun _ => ⟨SignalMap.emptyValues, trivial⟩
  hasStructuralResult := fun inputs state =>
    ⟨leafProposal (binary := binary) (identityModule := identityModule) inputs,
      leafProposal_satisfies inputs state⟩
  structuralResultUnique := leafUnique
  implements := leafImplements

private def nodeChildren
    {signalType : SignalType}
    {operation : signalType.Denote → signalType.Denote → signalType.Denote}
    {identity : signalType.Denote}
    {binary : BinaryImplementation signalType operation}
    {identityModule : IdentityImplementation signalType identity}
    (leftImplementation : Implementation binary identityModule left)
    (rightImplementation : Implementation binary identityModule right) :
    Certified.Children (nodeBody signalType left right)
  | .left => leftImplementation.bundle
  | .right => rightImplementation.bundle
  | .combine => binary.certified

private abbrev leftOccurrence
    {signalType : SignalType}
    {operation : signalType.Denote → signalType.Denote → signalType.Denote}
    {identity : signalType.Denote}
    {binary : BinaryImplementation signalType operation}
    {identityModule : IdentityImplementation signalType identity}
    (leftImplementation : Implementation binary identityModule left)
    (rightImplementation : Implementation binary identityModule right) :
    Certified.RuleOccurrence
      (nodeChildren leftImplementation rightImplementation) :=
  ⟨NodeInstance.left, Rule.apply⟩

private abbrev rightOccurrence
    {signalType : SignalType}
    {operation : signalType.Denote → signalType.Denote → signalType.Denote}
    {identity : signalType.Denote}
    {binary : BinaryImplementation signalType operation}
    {identityModule : IdentityImplementation signalType identity}
    (leftImplementation : Implementation binary identityModule left)
    (rightImplementation : Implementation binary identityModule right) :
    Certified.RuleOccurrence
      (nodeChildren leftImplementation rightImplementation) :=
  ⟨NodeInstance.right, Rule.apply⟩

private abbrev combineOccurrence
    {signalType : SignalType}
    {operation : signalType.Denote → signalType.Denote → signalType.Denote}
    {identity : signalType.Denote}
    {binary : BinaryImplementation signalType operation}
    {identityModule : IdentityImplementation signalType identity}
    (leftImplementation : Implementation binary identityModule left)
    (rightImplementation : Implementation binary identityModule right) :
    Certified.RuleOccurrence
      (nodeChildren leftImplementation rightImplementation) :=
  ⟨NodeInstance.combine, Rule.apply⟩

private def nodeOutputSchedule
    {signalType : SignalType}
    {operation : signalType.Denote → signalType.Denote → signalType.Denote}
    {identity : signalType.Denote}
    {binary : BinaryImplementation signalType operation}
    {identityModule : IdentityImplementation signalType identity}
    (leftImplementation : Implementation binary identityModule left)
    (rightImplementation : Implementation binary identityModule right) :
    Certified.OutputSchedule (nodeBody signalType left right)
      (nodeChildren leftImplementation rightImplementation)
      (cycleContract signalType operation identity (.node left right)) .apply :=
  .call (leftOccurrence leftImplementation rightImplementation)
    (by
      intro input _
      cases input with
      | leaf index =>
          change (Input.leaf (Fin.castAdd right.leafCount index) :
            Input (.node left right)) ∈
              (inputMap signalType (.node left right)).allSelection.labels
          rw [SignalMap.allSelection_labels]
          exact ListIndex.get_eq
            ((inputMap signalType (.node left right)).labels.locate
              (Input.leaf (Fin.castAdd right.leafCount index))) ▸ List.get_mem _ _)
    (by simp)
    (.call (rightOccurrence leftImplementation rightImplementation)
      (by
        intro input _
        cases input with
        | leaf index =>
            change (Input.leaf (Fin.natAdd left.leafCount index) :
              Input (.node left right)) ∈
                (inputMap signalType (.node left right)).allSelection.labels
            rw [SignalMap.allSelection_labels]
            exact ListIndex.get_eq
              ((inputMap signalType (.node left right)).labels.locate
                (Input.leaf (Fin.natAdd left.leafCount index))) ▸ List.get_mem _ _)
      (by
        intro member
        have equal := List.mem_singleton.mp member
        have childEqual := congrArg Certified.RuleOccurrence.child equal
        cases childEqual)
      (.call (combineOccurrence leftImplementation rightImplementation)
        (by
          intro input _
          cases input with
          | left =>
              refine ⟨Rule.apply, by simp, ?_⟩
              change Primitives.SingleOutput.output ∈
                (outputRule signalType operation identity left).writesOutputs.labels
              simp [outputRule, SignalMap.select, SignalSelection.labels]
          | right =>
              refine ⟨Rule.apply, by simp, ?_⟩
              change Primitives.SingleOutput.output ∈
                (outputRule signalType operation identity right).writesOutputs.labels
              simp [outputRule, SignalMap.select, SignalSelection.labels])
        (by
          intro member
          rcases List.mem_cons.mp member with equal | member
          · have childEqual := congrArg Certified.RuleOccurrence.child equal
            cases childEqual
          · have equal := List.mem_singleton.mp member
            have childEqual := congrArg Certified.RuleOccurrence.child equal
            cases childEqual)
        (.done (by
          intro outputName _
          cases outputName
          refine ⟨Rule.apply, by simp, ?_⟩
          change Primitives.SingleOutput.output ∈
            (binaryOutputRule signalType operation).writesOutputs.labels
          simp [binaryOutputRule, SignalMap.select, SignalSelection.labels]))))

private def nodeStateSchedule
    {signalType : SignalType}
    {operation : signalType.Denote → signalType.Denote → signalType.Denote}
    {identity : signalType.Denote}
    {binary : BinaryImplementation signalType operation}
    {identityModule : IdentityImplementation signalType identity}
    (leftImplementation : Implementation binary identityModule left)
    (rightImplementation : Implementation binary identityModule right) :
    Certified.StateSchedule (nodeBody signalType left right)
      (nodeChildren leftImplementation rightImplementation) :=
  .done (by
    intro child input member
    cases child with
    | left =>
        change input ∈ (CycleStateRule.empty (ports signalType left)).readsInputs.labels
          at member
        exact nomatch member
    | right =>
        change input ∈ (CycleStateRule.empty (ports signalType right)).readsInputs.labels
          at member
        exact nomatch member
    | combine =>
        change input ∈
          (CycleStateRule.empty (binaryPorts signalType)).readsInputs.labels at member
        exact nomatch member)

private def nodeRuleSchedules
    {signalType : SignalType}
    {operation : signalType.Denote → signalType.Denote → signalType.Denote}
    {identity : signalType.Denote}
    {binary : BinaryImplementation signalType operation}
    {identityModule : IdentityImplementation signalType identity}
    (leftImplementation : Implementation binary identityModule left)
    (rightImplementation : Implementation binary identityModule right) :
    Certified.RuleSchedules (nodeBody signalType left right)
      (nodeChildren leftImplementation rightImplementation)
      (cycleContract signalType operation identity (.node left right)) where
  output | .apply => nodeOutputSchedule leftImplementation rightImplementation
  state := nodeStateSchedule leftImplementation rightImplementation

private theorem nodeCoversChildren
    {signalType : SignalType}
    {operation : signalType.Denote → signalType.Denote → signalType.Denote}
    {identity : signalType.Denote}
    {binary : BinaryImplementation signalType operation}
    {identityModule : IdentityImplementation signalType identity}
    (leftImplementation : Implementation binary identityModule left)
    (rightImplementation : Implementation binary identityModule right) :
    (nodeRuleSchedules leftImplementation rightImplementation).CoversChildren := by
  intro child rule
  cases child with
  | left =>
      change Rule at rule
      cases rule
      apply Certified.RuleSchedules.Combined.add_preserves
      apply Certified.RuleSchedules.mem_combineOutputs
        (nodeRuleSchedules leftImplementation rightImplementation) .apply
      simp [nodeRuleSchedules, nodeOutputSchedule,
        Certified.Schedule.finalAvailability]
  | right =>
      change Rule at rule
      cases rule
      apply Certified.RuleSchedules.Combined.add_preserves
      apply Certified.RuleSchedules.mem_combineOutputs
        (nodeRuleSchedules leftImplementation rightImplementation) .apply
      simp [nodeRuleSchedules, nodeOutputSchedule,
        Certified.Schedule.finalAvailability]
  | combine =>
      change Rule at rule
      cases rule
      apply Certified.RuleSchedules.Combined.add_preserves
      apply Certified.RuleSchedules.mem_combineOutputs
        (nodeRuleSchedules leftImplementation rightImplementation) .apply
      simp [nodeRuleSchedules, nodeOutputSchedule,
        Certified.Schedule.finalAvailability]

private theorem nodeUnique
    {signalType : SignalType}
    {operation : signalType.Denote → signalType.Denote → signalType.Denote}
    {identity : signalType.Denote}
    {binary : BinaryImplementation signalType operation}
    {identityModule : IdentityImplementation signalType identity}
    (leftImplementation : Implementation binary identityModule left)
    (rightImplementation : Implementation binary identityModule right) :
    (moduleStructure binary identityModule (.node left right)).HasAtMostOneSolution := by
  have structure_eq : moduleStructure binary identityModule (.node left right) =
      Certified.moduleStructure (nodeBody signalType left right)
        (nodeChildren leftImplementation rightImplementation) := by
    apply congrArg (ModuleStructure.composite (nodeBody signalType left right))
    funext child
    cases child <;> rfl
  rw [structure_eq]
  exact (nodeRuleSchedules leftImplementation rightImplementation).hasAtMostOneSolution
    (nodeCoversChildren leftImplementation rightImplementation)

private def leftInputs (inputs : (ports signalType (.node left right)).inputs.Values) :
    (ports signalType left).inputs.Values
  | .leaf index => inputs (.leaf (Fin.castAdd right.leafCount index))

private def rightInputs (inputs : (ports signalType (.node left right)).inputs.Values) :
    (ports signalType right).inputs.Values
  | .leaf index => inputs (.leaf (Fin.natAdd left.leafCount index))

private def combineInputs
    {signalType : SignalType}
    {operation : signalType.Denote → signalType.Denote → signalType.Denote}
    {identity : signalType.Denote}
    {binary : BinaryImplementation signalType operation}
    {identityModule : IdentityImplementation signalType identity}
    (leftProposal : ProposedValues (moduleStructure binary identityModule left))
    (rightProposal : ProposedValues (moduleStructure binary identityModule right)) :
    (binaryPorts signalType).inputs.Values
  | .left => leftProposal.outputs .output
  | .right => rightProposal.outputs .output

private theorem nodeHasStructuralResult
    {signalType : SignalType}
    {operation : signalType.Denote → signalType.Denote → signalType.Denote}
    {identity : signalType.Denote}
    {binary : BinaryImplementation signalType operation}
    {identityModule : IdentityImplementation signalType identity}
    (leftImplementation : Implementation binary identityModule left)
    (rightImplementation : Implementation binary identityModule right)
    (inputs : (ports signalType (.node left right)).inputs.Values)
    (state : (moduleStructure binary identityModule (.node left right)).State) :
    ∃ proposal,
      (moduleStructure binary identityModule (.node left right)).IsSolution
        inputs state proposal := by
  rcases leftImplementation.hasStructuralResult (leftInputs inputs) (state .left) with
    ⟨leftProposal, leftSatisfies⟩
  rcases rightImplementation.hasStructuralResult (rightInputs inputs) (state .right) with
    ⟨rightProposal, rightSatisfies⟩
  rcases binary.certification.hasStructuralResult
      (combineInputs leftProposal rightProposal) (state .combine) with
    ⟨combineProposal, combineSatisfies⟩
  let outputs : (ports signalType (.node left right)).outputs.Values := fun
    | .output => combineProposal.outputs .output
  let proposal : ProposedValues
      (moduleStructure binary identityModule (.node left right)) :=
    ProposedValues.composite outputs fun
      | .left => leftProposal
      | .right => rightProposal
      | .combine => combineProposal
  refine ⟨proposal, ?_⟩
  constructor
  · intro outputName
    cases outputName
    rfl
  · intro child
    cases child with
    | left =>
        change (moduleStructure binary identityModule left).IsSolution
          (ProposedValues.childInputs (nodeBody signalType left right) _ inputs
            proposal.2 .left) (state .left) leftProposal
        rw [show ProposedValues.childInputs (nodeBody signalType left right) _ inputs
            proposal.2 .left = leftInputs inputs by
          funext input
          cases input
          rfl]
        exact leftSatisfies
    | right =>
        change (moduleStructure binary identityModule right).IsSolution
          (ProposedValues.childInputs (nodeBody signalType left right) _ inputs
            proposal.2 .right) (state .right) rightProposal
        rw [show ProposedValues.childInputs (nodeBody signalType left right) _ inputs
            proposal.2 .right = rightInputs inputs by
          funext input
          cases input
          rfl]
        exact rightSatisfies
    | combine =>
        change binary.moduleStructure.IsSolution
          (ProposedValues.childInputs (nodeBody signalType left right) _ inputs
            proposal.2 .combine) (state .combine) combineProposal
        rw [show ProposedValues.childInputs (nodeBody signalType left right) _ inputs
            proposal.2 .combine = combineInputs leftProposal rightProposal by
          funext input
          cases input <;> rfl]
        exact combineSatisfies

private def nodeStateCorresponds
    {signalType : SignalType}
    {operation : signalType.Denote → signalType.Denote → signalType.Denote}
    {identity : signalType.Denote}
    {binary : BinaryImplementation signalType operation}
    {identityModule : IdentityImplementation signalType identity}
    (leftImplementation : Implementation binary identityModule left)
    (rightImplementation : Implementation binary identityModule right)
    (_ : emptySignalMap.Values)
    (state : (moduleStructure binary identityModule (.node left right)).State) : Prop :=
  leftImplementation.stateCorresponds SignalMap.emptyValues (state .left) ∧
    rightImplementation.stateCorresponds SignalMap.emptyValues (state .right) ∧
    binary.certification.stateCorresponds SignalMap.emptyValues (state .combine)

private theorem nodeImplements
    {signalType : SignalType}
    {operation : signalType.Denote → signalType.Denote → signalType.Denote}
    {identity : signalType.Denote}
    {binary : BinaryImplementation signalType operation}
    {identityModule : IdentityImplementation signalType identity}
    (leftImplementation : Implementation binary identityModule left)
    (rightImplementation : Implementation binary identityModule right) :
    Implements (moduleStructure binary identityModule (.node left right))
      (cycleContract signalType operation identity (.node left right))
      (nodeStateCorresponds leftImplementation rightImplementation) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, children⟩
  rcases satisfies with ⟨boundary, childSatisfies⟩
  have leftInputs_eq : ProposedValues.childInputs
      (nodeBody signalType left right) _ inputs children .left = leftInputs inputs := by
    funext input
    cases input
    rfl
  have rightInputs_eq : ProposedValues.childInputs
      (nodeBody signalType left right) _ inputs children .right = rightInputs inputs := by
    funext input
    cases input
    rfl
  have combineInputs_eq : ProposedValues.childInputs
      (nodeBody signalType left right) _ inputs children .combine =
        combineInputs (children .left) (children .right) := by
    funext input
    cases input <;> rfl
  have leftSatisfies := childSatisfies .left
  rw [leftInputs_eq] at leftSatisfies
  have rightSatisfies := childSatisfies .right
  rw [rightInputs_eq] at rightSatisfies
  have combineSatisfies := childSatisfies .combine
  rw [combineInputs_eq] at combineSatisfies
  rcases leftImplementation.implements (leftInputs inputs) SignalMap.emptyValues
      (structuralState .left) (children .left) corresponds.1 leftSatisfies with
    ⟨leftNext, leftEvaluates, leftNextCorresponds⟩
  rcases rightImplementation.implements (rightInputs inputs) SignalMap.emptyValues
      (structuralState .right) (children .right) corresponds.2.1 rightSatisfies with
    ⟨rightNext, rightEvaluates, rightNextCorresponds⟩
  rcases binary.certification.implements
      (combineInputs (children .left) (children .right)) SignalMap.emptyValues
      (structuralState .combine) (children .combine) corresponds.2.2
      combineSatisfies with
    ⟨combineNext, combineEvaluates, combineNextCorresponds⟩
  have leftNext_eq : leftNext = SignalMap.emptyValues := by
    funext impossible
    exact nomatch impossible
  have rightNext_eq : rightNext = SignalMap.emptyValues := by
    funext impossible
    exact nomatch impossible
  have combineNext_eq : combineNext = SignalMap.emptyValues := by
    funext impossible
    exact nomatch impossible
  subst leftNext
  subst rightNext
  subst combineNext
  refine ⟨SignalMap.emptyValues, ?_, ?_⟩
  · constructor
    · intro rule
      cases rule
      rw [outputRule_holds_iff]
      have leftEquation := leftEvaluates.1 Rule.apply
      rw [outputRule_holds_iff] at leftEquation
      have rightEquation := rightEvaluates.1 Rule.apply
      rw [outputRule_holds_iff] at rightEquation
      have combineEquation := combineEvaluates.1 Rule.apply
      rw [binaryOutputRule_holds_iff] at combineEquation
      simp only [combineInputs] at combineEquation
      have outputBoundary := boundary Primitives.SingleOutput.output
      change outputs Primitives.SingleOutput.output = (children .combine).outputs Primitives.SingleOutput.output at outputBoundary
      change outputs Primitives.SingleOutput.output = _
      rw [outputBoundary, combineEquation, leftEquation, rightEquation]
      rfl
    · rfl
  · exact ⟨leftNextCorresponds, rightNextCorresponds, combineNextCorresponds⟩

private def nodeImplementation
    {signalType : SignalType}
    {operation : signalType.Denote → signalType.Denote → signalType.Denote}
    {identity : signalType.Denote}
    {binary : BinaryImplementation signalType operation}
    {identityModule : IdentityImplementation signalType identity}
    (leftImplementation : Implementation binary identityModule left)
    (rightImplementation : Implementation binary identityModule right) :
    Implementation binary identityModule (.node left right) where
  stateCorresponds := nodeStateCorresponds leftImplementation rightImplementation
  hasCorrespondingState := by
    intro state
    rcases leftImplementation.hasCorrespondingState (state .left) with
      ⟨leftState, leftCorresponds⟩
    rcases rightImplementation.hasCorrespondingState (state .right) with
      ⟨rightState, rightCorresponds⟩
    rcases binary.certification.hasCorrespondingState (state .combine) with
      ⟨combineState, combineCorresponds⟩
    have leftState_eq : leftState = SignalMap.emptyValues := by
      funext impossible
      exact nomatch impossible
    have rightState_eq : rightState = SignalMap.emptyValues := by
      funext impossible
      exact nomatch impossible
    have combineState_eq : combineState = SignalMap.emptyValues := by
      funext impossible
      exact nomatch impossible
    subst leftState
    subst rightState
    subst combineState
    exact ⟨SignalMap.emptyValues,
      leftCorresponds, rightCorresponds, combineCorresponds⟩
  hasStructuralResult :=
    nodeHasStructuralResult leftImplementation rightImplementation
  structuralResultUnique := nodeUnique leftImplementation rightImplementation
  implements := nodeImplements leftImplementation rightImplementation

private def implementation (binary : BinaryImplementation signalType operation)
    (identityModule : IdentityImplementation signalType identity) :
    (tree : Tree) → Implementation binary identityModule tree
  | .empty => emptyImplementation identityModule
  | .leaf => leafImplementation
  | .node left right =>
      nodeImplementation (implementation binary identityModule left)
        (implementation binary identityModule right)

def certification (binary : BinaryImplementation signalType operation)
    (identityModule : IdentityImplementation signalType identity) (tree : Tree) :
    ModuleCycleCertification (moduleStructure binary identityModule tree)
      (cycleContract signalType operation identity tree) :=
  implementation binary identityModule tree

def certified (binary : BinaryImplementation signalType operation)
    (identityModule : IdentityImplementation signalType identity)
    (tree : Tree) : ModuleCycleCertified (ports signalType tree) :=
  (certification binary identityModule tree).bundle

@[simp] theorem certified_moduleStructure
    (binary : BinaryImplementation signalType operation)
    (identityModule : IdentityImplementation signalType identity) (tree : Tree) :
    (certified binary identityModule tree).moduleStructure =
      moduleStructure binary identityModule tree := rfl

@[simp] theorem certified_cycleContract
    (binary : BinaryImplementation signalType operation)
    (identityModule : IdentityImplementation signalType identity) (tree : Tree) :
    (certified binary identityModule tree).cycleContract =
      cycleContract signalType operation identity tree := rfl

end Silean.Modules.Reduction

namespace Silean.Modules.Reduction.Naming

open Silean Silean.Naming

def ports (signalType : SignalType) (tree : Tree) :
    ModulePortsNaming (Reduction.ports signalType tree) where
  inputs := SignalMapNaming.indexed _ "input"
  outputs := ⟨fun | .output => "result"⟩

private def treeParameters : Tree → List ModuleParameter
  | .empty => [.natural 0]
  | .leaf => [.natural 1]
  | .node left right =>
      .natural 2 :: treeParameters left ++ treeParameters right

def naming (family : String)
    (binary : BinaryImplementation signalType operation)
    (identityModule : IdentityImplementation signalType identity)
    (binaryNaming : ModuleNaming binary.moduleStructure)
    (identityNaming : ModuleNaming identityModule.moduleStructure) :
    (tree : Tree) → ModuleNaming
      (Reduction.moduleStructure binary identityModule tree)
  | .empty => .composite
      ⟨family, "empty", .shape signalType :: treeParameters .empty⟩
      (ports signalType .empty)
      (fun | .identity => "identity")
      (fun | .identity => identityNaming)
  | .leaf => .composite
      ⟨family, "leaf", .shape signalType :: treeParameters .leaf⟩
      (ports signalType .leaf)
      (fun impossible => nomatch impossible)
      (fun impossible => nomatch impossible)
  | .node left right => .composite
      ⟨family, "node", .shape signalType :: treeParameters (.node left right)⟩
      (ports signalType (.node left right))
      (fun
        | .left => "left"
        | .right => "right"
        | .combine => "combine")
      (fun
        | .left => naming family binary identityModule binaryNaming identityNaming left
        | .right => naming family binary identityModule binaryNaming identityNaming right
        | .combine => binaryNaming)

end Silean.Modules.Reduction.Naming
