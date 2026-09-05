import Silean.Contracts.Cycle.CycleLayerConstruction
import Silean.Contracts.Cycle.CycleScheduleDerivation

namespace Silean.Composition.Reduction

open Silean
open Contracts.Cycle.Certification.Layer

/-! A reduction tree records hierarchy shape independently of the operation
being reduced. Keeping the leaf count as a computed property makes recursive
module construction substantially clearer than carrying arithmetic equalities
through every node. -/

inductive Tree where
  /-- Identity-only reduction with no inputs. -/
  | empty
  /-- A single unreduced input. -/
  | leaf
  /-- Combines the results of two subtrees. -/
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

/-! ## Width-indexed balanced reductions

These helpers give specializations a common balanced tree and port boundary
for a requested public width. -/

def balancedTree (width : Nat) : Tree := Tree.balanced width

@[reducible] def balancedPorts (signalType : SignalType) (width : Nat) : ModulePorts :=
  ports signalType (balancedTree width)

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
    Contracts.Cycle.CycleOutputRule (ports signalType tree) emptySignalMap where
  readsInputs := .all (inputMap signalType tree)
  writesOutputs := .all (outputMap signalType)
  target inputs _ := fun
    | .output => fold operation identity tree fun index => inputs (.leaf index)

@[reducible] def cycleContract (signalType : SignalType)
    (operation : signalType.Denote → signalType.Denote → signalType.Denote)
    (identity : signalType.Denote) (tree : Tree) :
    Contracts.Cycle.ModuleCycleContract (ports signalType tree) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => outputRule signalType operation identity tree
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem outputRule_holds_iff (inputs : (ports signalType tree).inputs.Values)
    (state : emptySignalMap.Values) (outputs : (ports signalType tree).outputs.Values) :
    (outputRule signalType operation identity tree).Holds inputs state outputs ↔
      outputs .output = fold operation identity tree (fun index =>
        inputs (.leaf index)) := by
  simp only [outputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal
    exact congrFun equal .output
  · intro equal
    funext label
    cases label
    exact equal

def binaryOutputRule (signalType : SignalType)
    (operation : signalType.Denote → signalType.Denote → signalType.Denote) :
    Contracts.Cycle.CycleOutputRule (binaryPorts signalType) emptySignalMap where
  readsInputs := .all (binaryInputMap signalType)
  writesOutputs := .all (outputMap signalType)
  target inputs _ := fun | .output => operation (inputs .left) (inputs .right)

@[reducible] def binaryCycleContract (signalType : SignalType)
    (operation : signalType.Denote → signalType.Denote → signalType.Denote) :
    Contracts.Cycle.ModuleCycleContract (binaryPorts signalType) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => binaryOutputRule signalType operation
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem binaryOutputRule_holds_iff
    (inputs : (binaryPorts signalType).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (binaryPorts signalType).outputs.Values) :
    (binaryOutputRule signalType operation).Holds inputs state outputs ↔
      outputs .output = operation (inputs .left) (inputs .right) := by
  simp only [binaryOutputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal
    exact congrFun equal .output
  · intro equal
    funext label
    cases label
    exact equal

abbrev BinaryImplementation (signalType : SignalType)
    (operation : signalType.Denote → signalType.Denote → signalType.Denote) :=
  Contracts.Cycle.ModuleCycleCertifiedStructure
    (binaryCycleContract signalType operation)

def BinaryImplementation.certified
    (implementation : BinaryImplementation signalType operation) :
    Contracts.Cycle.ModuleCycleCertified (binaryPorts signalType) :=
  implementation.certification.bundle

@[reducible] def identityPorts (signalType : SignalType) : ModulePorts :=
  ⟨emptySignalMap, outputMap signalType⟩

def identityOutputRule (signalType : SignalType) (identity : signalType.Denote) :
    Contracts.Cycle.CycleOutputRule (identityPorts signalType) emptySignalMap where
  readsInputs := .empty (identityPorts signalType).inputs
  writesOutputs := .all (outputMap signalType)
  target _ _ := fun | .output => identity

@[reducible] def identityCycleContract (signalType : SignalType)
    (identity : signalType.Denote) : Contracts.Cycle.ModuleCycleContract (identityPorts signalType) where
  state := emptySignalMap
  RuleName := Rule
  ruleNames := inferInstance
  outputRule | .apply => identityOutputRule signalType identity
  stateRule := Contracts.Cycle.CycleStateRule.empty _
  outputCoverage := by rfl

@[simp] theorem identityOutputRule_holds_iff
    (inputs : (identityPorts signalType).inputs.Values)
    (state : emptySignalMap.Values)
    (outputs : (identityPorts signalType).outputs.Values) :
    (identityOutputRule signalType identity).Holds inputs state outputs ↔
      outputs .output = identity := by
  simp only [identityOutputRule, Contracts.Cycle.CycleOutputRule.Holds,
    SignalGroup.all_matches]
  constructor
  · intro equal
    exact congrFun equal .output
  · intro equal
    funext label
    cases label
    exact equal

abbrev IdentityImplementation (signalType : SignalType)
    (identity : signalType.Denote) :=
  Contracts.Cycle.ModuleCycleCertifiedStructure
    (identityCycleContract signalType identity)

def IdentityImplementation.certified
    (implementation : IdentityImplementation signalType identity) :
    Contracts.Cycle.ModuleCycleCertified (identityPorts signalType) :=
  implementation.certification.bundle

inductive EmptyInstance | identity
deriving Enumeration

private def emptyInstances (signalType : SignalType) : InstancePorts :=
  EnumeratedMap.of EmptyInstance fun | .identity => identityPorts signalType

private def emptyContext (signalType : SignalType) : EndpointContext where
  ports := ports signalType .empty
  instancePorts := emptyInstances signalType

private def emptyWiring (signalType : SignalType) :
    Wiring (emptyContext signalType).ports (emptyContext signalType).instancePorts where
  moduleOutput := fun outputName => match outputName with
    | Primitives.SingleOutput.output =>
        (emptyContext signalType).instanceOutput EmptyInstance.identity Primitives.SingleOutput.output
  instanceInput := fun child input => match child with
    | EmptyInstance.identity => nomatch input

private def emptyBody (signalType : SignalType) : ModuleBody :=
  ⟨emptyContext signalType, emptyWiring signalType⟩

private def emptyChildContracts (signalType : SignalType)
    (identity : signalType.Denote) :
    Contracts.Cycle.ChildCycleContracts (emptyBody signalType)
  | .identity => identityCycleContract signalType identity

private def emptyStructuralChildren
    (implementation : IdentityImplementation signalType identity) :
    (child : EmptyInstance) →
      ModuleStructure ((emptyInstances signalType).ports child)
  | .identity => implementation.moduleStructure

private def emptyCertifiedChildren
    (implementation : IdentityImplementation signalType identity) :
    (child : EmptyInstance) →
      Contracts.Cycle.ModuleCycleCertifiedStructure
        (emptyChildContracts signalType identity child)
  | .identity => implementation

inductive LeafInstance

private instance : Enumeration LeafInstance :=
  Enumeration.empty fun impossible => nomatch impossible

@[reducible] private def leafInstances : InstancePorts :=
  EnumeratedMap.of LeafInstance fun impossible => nomatch impossible

@[reducible] private def leafContext (signalType : SignalType) : EndpointContext where
  ports := ports signalType .leaf
  instancePorts := leafInstances

@[reducible] private def leafWiring (signalType : SignalType) :
    Wiring (leafContext signalType).ports (leafContext signalType).instancePorts where
  moduleOutput := fun outputName => match outputName with
    | Primitives.SingleOutput.output => (leafContext signalType).moduleInput
        (Input.leaf ⟨0, by simp [Tree.leafCount]⟩)
  instanceInput := fun impossible _ => nomatch impossible

@[reducible] private def leafBody (signalType : SignalType) : ModuleBody :=
  ⟨leafContext signalType, leafWiring signalType⟩

/-! ## Hardware structure -/

inductive NodeInstance
  /-- Reduces the left group of leaves. -/
  | left
  /-- Reduces the right group of leaves. -/
  | right
  /-- Applies the binary operation to both subtree results. -/
  | combine
deriving Enumeration

@[reducible] private def nodeInstances (signalType : SignalType) (left right : Tree) : InstancePorts :=
  EnumeratedMap.of NodeInstance fun
    | .left => ports signalType left
    | .right => ports signalType right
    | .combine => binaryPorts signalType

@[reducible] private def nodeContext (signalType : SignalType) (left right : Tree) :
    EndpointContext where
  ports := ports signalType (.node left right)
  instancePorts := nodeInstances signalType left right

@[reducible] private def nodeWiring (signalType : SignalType) (left right : Tree) :
    Wiring (nodeContext signalType left right).ports
      (nodeContext signalType left right).instancePorts where
  moduleOutput := fun outputName => match outputName with
    -- The binary combiner produces the node result.
    | Primitives.SingleOutput.output => (nodeContext signalType left right).instanceOutput
        NodeInstance.combine Primitives.SingleOutput.output
  instanceInput := fun
    -- Partition the input leaves between the two subtrees.
    | NodeInstance.left, Input.leaf index =>
        (nodeContext signalType left right).moduleInput
          (Input.leaf (Fin.castAdd right.leafCount index))
    | NodeInstance.right, Input.leaf index =>
        (nodeContext signalType left right).moduleInput
          (Input.leaf (Fin.natAdd left.leafCount index))
    -- Combine the two recursively reduced values.
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

/-- A reduction tree contains no blackboxes when its binary operation and
empty-tree identity modules contain no blackboxes. -/
private abbrev Implementation (binary : BinaryImplementation signalType operation)
    (identityModule : IdentityImplementation signalType identity)
    (tree : Tree) := Contracts.Cycle.ModuleCycleCertification
      (moduleStructure binary identityModule tree)
      (cycleContract signalType operation identity tree)

private abbrev emptyOccurrence
    (signalType : SignalType) (identity : signalType.Denote) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (emptyBody signalType) (emptyChildContracts (signalType := signalType)
        (identity := identity)) :=
  ⟨EmptyInstance.identity, Rule.apply⟩

private def emptyScheduleOrders
    (signalType : SignalType) (operation : signalType.Denote → signalType.Denote → signalType.Denote)
    (identity : signalType.Denote) :
    ScheduleDerivation.RuleScheduleOrders (emptyBody signalType)
      (emptyChildContracts (signalType := signalType) (identity := identity))
      (cycleContract signalType operation identity .empty) where
  output | .apply => [emptyOccurrence signalType identity]
  state := []

private def emptyDerivedRuleSchedules
    (signalType : SignalType) (operation : signalType.Denote → signalType.Denote → signalType.Denote)
    (identity : signalType.Denote) :
    ScheduleDerivation.DerivedRuleSchedules (emptyBody signalType)
      (emptyChildContracts (signalType := signalType) (identity := identity))
      (cycleContract signalType operation identity .empty) := by
  derive_rule_schedules (emptyScheduleOrders signalType operation identity)

private abbrev emptyRuleSchedules (signalType : SignalType)
    (operation : signalType.Denote → signalType.Denote → signalType.Denote)
    (identity : signalType.Denote) :=
  (emptyDerivedRuleSchedules signalType operation identity).schedules

private theorem emptyCoversChildren (signalType : SignalType)
    (operation : signalType.Denote → signalType.Denote → signalType.Denote)
    (identity : signalType.Denote) :
    (emptyRuleSchedules signalType operation identity).CoversChildren :=
  (emptyDerivedRuleSchedules signalType operation identity).coversChildren

section EmptyLayerCertification

variable (signalType : SignalType)
  (operation : signalType.Denote → signalType.Denote → signalType.Denote)
  (identity : signalType.Denote)
  (layerChildren : (child : EmptyInstance) →
    Contracts.Cycle.ModuleCycleCertifiedStructure
      (emptyChildContracts (signalType := signalType) (identity := identity) child))

private abbrev emptyCertificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure (emptyBody signalType) layerChildren

private def emptyStateCorresponds
    (_ : emptySignalMap.Values)
    (_ : (emptyCertificationStructure signalType identity layerChildren).State) : Prop := True

private theorem emptyImplements
    : Contracts.Cycle.Implements
      (emptyCertificationStructure signalType identity layerChildren)
      (cycleContract signalType operation identity .empty)
      (emptyStateCorresponds signalType identity layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, children⟩
  have boundary := satisfies.1
  letI : Subsingleton
      ((emptyChildContracts (signalType := signalType) (identity := identity) .identity).state.Values) := by
    change Subsingleton emptySignalMap.Values
    infer_instance
  have evaluates :=
    (Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren inputs
        structuralState (ProposedValues.composite outputs children) satisfies
        .identity SignalMap.emptyValues).1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  constructor
  · intro rule
    cases rule
    change (outputRule signalType operation identity .empty).Holds
      inputs contractState outputs
    rw [outputRule_holds_iff]
    have identityEquation := evaluates.1 Rule.apply
    change (identityOutputRule signalType identity).Holds _ _ _ at identityEquation
    rw [identityOutputRule_holds_iff] at identityEquation
    exact (boundary .output).trans identityEquation
  · rfl

end EmptyLayerCertification

private noncomputable opaque emptyCertifiedLayer
    (signalType : SignalType)
    (operation : signalType.Denote → signalType.Denote → signalType.Denote)
    (identity : signalType.Denote) :
    Contracts.Cycle.ModuleCycleCertifiedLayer (emptyBody signalType)
      (emptyChildContracts (signalType := signalType) (identity := identity))
      (cycleContract signalType operation identity .empty) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (emptyRuleSchedules signalType operation identity)
    (emptyCoversChildren signalType operation identity)
    (emptyStateCorresponds signalType identity)
    (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩)
    (emptyImplements signalType operation identity)

private noncomputable def emptyImplementation
    {signalType : SignalType}
    {operation : signalType.Denote → signalType.Denote → signalType.Denote}
    {identity : signalType.Denote}
    {binary : BinaryImplementation signalType operation}
    (identityModule : IdentityImplementation signalType identity) :
    Implementation binary identityModule .empty :=
  (emptyCertifiedLayer signalType operation identity).certifyComposite
    (emptyStructuralChildren identityModule)
    (emptyCertifiedChildren identityModule)
    (by intro child; cases child; rfl)

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
    Contracts.Cycle.Implements (moduleStructure (signalType := signalType) binary identityModule .leaf)
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

private def nodeChildContracts
    (signalType : SignalType)
    (operation : signalType.Denote → signalType.Denote → signalType.Denote)
    (identity : signalType.Denote) (left right : Tree) :
    Contracts.Cycle.ChildCycleContracts (nodeBody signalType left right)
  | .left => cycleContract signalType operation identity left
  | .right => cycleContract signalType operation identity right
  | .combine => binaryCycleContract signalType operation

private def nodeStructuralChildren
    {signalType : SignalType} {operation} {identity}
    {binary : BinaryImplementation signalType operation}
    {identityModule : IdentityImplementation signalType identity}
    (_leftImplementation : Implementation binary identityModule left)
    (_rightImplementation : Implementation binary identityModule right) :
    (child : NodeInstance) →
      ModuleStructure ((nodeInstances signalType left right).ports child)
  | .left => moduleStructure binary identityModule left
  | .right => moduleStructure binary identityModule right
  | .combine => binary.moduleStructure

private def nodeCertifiedChildren
    {signalType : SignalType} {operation} {identity}
    {binary : BinaryImplementation signalType operation}
    {identityModule : IdentityImplementation signalType identity}
    (leftImplementation : Implementation binary identityModule left)
    (rightImplementation : Implementation binary identityModule right) :
    (child : NodeInstance) → Contracts.Cycle.ModuleCycleCertifiedStructure
      (nodeChildContracts signalType operation identity left right child)
  | .left => ⟨moduleStructure binary identityModule left, leftImplementation⟩
  | .right => ⟨moduleStructure binary identityModule right, rightImplementation⟩
  | .combine => binary

private abbrev leftOccurrence
    {signalType : SignalType}
    {operation : signalType.Denote → signalType.Denote → signalType.Denote}
    {identity : signalType.Denote}
    (left right : Tree) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (nodeBody signalType left right)
      (nodeChildContracts signalType operation identity left right) :=
  ⟨NodeInstance.left, Rule.apply⟩

private abbrev rightOccurrence
    {signalType : SignalType}
    {operation : signalType.Denote → signalType.Denote → signalType.Denote}
    {identity : signalType.Denote}
    (left right : Tree) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (nodeBody signalType left right)
      (nodeChildContracts signalType operation identity left right) :=
  ⟨NodeInstance.right, Rule.apply⟩

private abbrev combineOccurrence
    {signalType : SignalType}
    {operation : signalType.Denote → signalType.Denote → signalType.Denote}
    {identity : signalType.Denote}
    (left right : Tree) :
    Contracts.Cycle.Certification.Layer.RuleOccurrence
      (nodeBody signalType left right)
      (nodeChildContracts signalType operation identity left right) :=
  ⟨NodeInstance.combine, Rule.apply⟩

private def nodeScheduleOrders
    (signalType : SignalType)
    (operation : signalType.Denote → signalType.Denote → signalType.Denote)
    (identity : signalType.Denote) (left right : Tree) :
    ScheduleDerivation.RuleScheduleOrders (nodeBody signalType left right)
      (nodeChildContracts signalType operation identity left right)
      (cycleContract signalType operation identity (.node left right)) where
  output := fun
    | .apply =>
        [leftOccurrence (operation := operation) (identity := identity) left right,
          rightOccurrence (operation := operation) (identity := identity) left right,
          combineOccurrence (operation := operation) (identity := identity) left right]
  state := []

private def nodeDerivedRuleSchedules
    (signalType : SignalType)
    (operation : signalType.Denote → signalType.Denote → signalType.Denote)
    (identity : signalType.Denote) (left right : Tree) :
    ScheduleDerivation.DerivedRuleSchedules (nodeBody signalType left right)
      (nodeChildContracts signalType operation identity left right)
      (cycleContract signalType operation identity (.node left right)) := by
  derive_rule_schedules (nodeScheduleOrders signalType operation identity left right)

private abbrev nodeRuleSchedules (signalType : SignalType)
    (operation : signalType.Denote → signalType.Denote → signalType.Denote)
    (identity : signalType.Denote) (left right : Tree) :=
  (nodeDerivedRuleSchedules signalType operation identity left right).schedules

private theorem nodeCoversChildren (signalType : SignalType)
    (operation : signalType.Denote → signalType.Denote → signalType.Denote)
    (identity : signalType.Denote) (left right : Tree) :
    (nodeRuleSchedules signalType operation identity left right).CoversChildren :=
  (nodeDerivedRuleSchedules signalType operation identity left right).coversChildren

private def leftInputs (inputs : (ports signalType (.node left right)).inputs.Values) :
    (ports signalType left).inputs.Values
  | .leaf index => inputs (.leaf (Fin.castAdd right.leafCount index))

private def rightInputs (inputs : (ports signalType (.node left right)).inputs.Values) :
    (ports signalType right).inputs.Values
  | .leaf index => inputs (.leaf (Fin.natAdd left.leafCount index))

private def combineInputs
    {signalType : SignalType}
    (leftOutputs rightOutputs : (outputMap signalType).Values) :
    (binaryPorts signalType).inputs.Values
  | .left => leftOutputs .output
  | .right => rightOutputs .output

section NodeLayerCertification

variable (signalType : SignalType)
  (operation : signalType.Denote → signalType.Denote → signalType.Denote)
  (identity : signalType.Denote) (left right : Tree)
  (layerChildren : (child : NodeInstance) →
    Contracts.Cycle.ModuleCycleCertifiedStructure
      (nodeChildContracts signalType operation identity left right child))

private abbrev nodeCertificationStructure :=
  Contracts.Cycle.Certification.Layer.moduleStructure (nodeBody signalType left right) layerChildren

private def nodeStateCorresponds (_ : emptySignalMap.Values)
    (_ : (nodeCertificationStructure signalType operation identity left right
      layerChildren).State) : Prop := True

private theorem nodeImplements :
    Contracts.Cycle.Implements
      (nodeCertificationStructure signalType operation identity left right layerChildren)
      (cycleContract signalType operation identity (.node left right))
      (nodeStateCorresponds signalType operation identity left right layerChildren) := by
  intro inputs contractState structuralState proposal corresponds satisfies
  rcases proposal with ⟨outputs, children⟩
  have boundary := satisfies.1
  have childMatch (child : NodeInstance) := by
    letI : Subsingleton
        ((nodeChildContracts signalType operation identity left right child).state.Values) := by
      cases child <;> change Subsingleton emptySignalMap.Values <;> infer_instance
    exact Contracts.Cycle.Certification.Layer.childSolutionMatchesContract_of_subsingletonState
      layerChildren
        inputs structuralState (ProposedValues.composite outputs children) satisfies child
        (by cases child <;> exact SignalMap.emptyValues)
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
        combineInputs (children .left).outputs (children .right).outputs := by
    funext input
    cases input <;> rfl
  have leftEvaluates := (childMatch .left).1
  have rightEvaluates := (childMatch .right).1
  have combineEvaluates := (childMatch .combine).1
  refine ⟨SignalMap.emptyValues, ?_, trivial⟩
  · constructor
    · intro rule
      cases rule
      rw [outputRule_holds_iff]
      have leftEquation := leftEvaluates.1 Rule.apply
      change (outputRule signalType operation identity left).Holds _ _ _ at leftEquation
      rw [outputRule_holds_iff] at leftEquation
      change (children .left).outputs .output =
        fold operation identity left fun index =>
          ProposedValues.childInputs (nodeBody signalType left right)
            ((fun name => (layerChildren name).moduleStructure))
            inputs children .left (.leaf index) at leftEquation
      have rightEquation := rightEvaluates.1 Rule.apply
      change (outputRule signalType operation identity right).Holds _ _ _ at rightEquation
      rw [outputRule_holds_iff] at rightEquation
      change (children .right).outputs .output =
        fold operation identity right fun index =>
          ProposedValues.childInputs (nodeBody signalType left right)
            ((fun name => (layerChildren name).moduleStructure))
            inputs children .right (.leaf index) at rightEquation
      have combineEquation := combineEvaluates.1 Rule.apply
      change (binaryOutputRule signalType operation).Holds _ _ _ at combineEquation
      rw [binaryOutputRule_holds_iff] at combineEquation
      change (children .combine).outputs .output = operation
        (ProposedValues.childInputs (nodeBody signalType left right)
          ((fun name => (layerChildren name).moduleStructure))
          inputs children .combine .left)
        (ProposedValues.childInputs (nodeBody signalType left right)
          ((fun name => (layerChildren name).moduleStructure))
          inputs children .combine .right) at combineEquation
      rw [leftInputs_eq] at leftEquation
      rw [rightInputs_eq] at rightEquation
      rw [combineInputs_eq] at combineEquation
      simp only [combineInputs] at combineEquation
      have outputBoundary := boundary Primitives.SingleOutput.output
      change outputs Primitives.SingleOutput.output = (children .combine).outputs Primitives.SingleOutput.output at outputBoundary
      change outputs Primitives.SingleOutput.output = _
      rw [outputBoundary, combineEquation, leftEquation, rightEquation]
      rfl
    · rfl

end NodeLayerCertification

private noncomputable opaque nodeCertifiedLayer
    (signalType : SignalType)
    (operation : signalType.Denote → signalType.Denote → signalType.Denote)
    (identity : signalType.Denote) (left right : Tree) :
    Contracts.Cycle.ModuleCycleCertifiedLayer (nodeBody signalType left right)
      (nodeChildContracts signalType operation identity left right)
      (cycleContract signalType operation identity (.node left right)) :=
  Contracts.Cycle.Certification.Layer.RuleSchedules.certifiedLayer
    (nodeRuleSchedules signalType operation identity left right)
    (nodeCoversChildren signalType operation identity left right)
    (nodeStateCorresponds signalType operation identity left right)
    (fun _ _ => ⟨SignalMap.emptyValues, trivial⟩)
    (nodeImplements signalType operation identity left right)

private noncomputable def nodeImplementation
    {signalType : SignalType}
    {operation : signalType.Denote → signalType.Denote → signalType.Denote}
    {identity : signalType.Denote}
    {binary : BinaryImplementation signalType operation}
    {identityModule : IdentityImplementation signalType identity}
    (leftImplementation : Implementation binary identityModule left)
    (rightImplementation : Implementation binary identityModule right) :
    Implementation binary identityModule (.node left right) := by
  let certification :=
    (nodeCertifiedLayer signalType operation identity left right).certifyComposite
      (nodeStructuralChildren leftImplementation rightImplementation)
      (nodeCertifiedChildren leftImplementation rightImplementation)
      (by intro child; cases child <;> rfl)
  have structureEqual :
      ModuleStructure.composite (nodeBody signalType left right)
        (nodeStructuralChildren leftImplementation rightImplementation) =
      moduleStructure binary identityModule (.node left right) := by
    rw [moduleStructure]
    congr
    funext child
    cases child <;> rfl
  exact certification.transportStructure structureEqual

private noncomputable def implementation (binary : BinaryImplementation signalType operation)
    (identityModule : IdentityImplementation signalType identity) :
    (tree : Tree) → Implementation binary identityModule tree
  | .empty => emptyImplementation identityModule
  | .leaf => leafImplementation
  | .node left right =>
      nodeImplementation (implementation binary identityModule left)
        (implementation binary identityModule right)

noncomputable def certification (binary : BinaryImplementation signalType operation)
    (identityModule : IdentityImplementation signalType identity) (tree : Tree) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure binary identityModule tree)
      (cycleContract signalType operation identity tree) :=
  implementation binary identityModule tree

noncomputable def certified (binary : BinaryImplementation signalType operation)
    (identityModule : IdentityImplementation signalType identity)
    (tree : Tree) : Contracts.Cycle.ModuleCycleCertified (ports signalType tree) :=
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

end Silean.Composition.Reduction
