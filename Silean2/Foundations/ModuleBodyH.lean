import Silean2.Foundations.PortsH
import Silean2.Foundations.TraceH

namespace Silean2.Foundations

abbrev ChildPorts (nChildren : Nat) := Fin nChildren → ModulePorts

-- We want to encode the signal type in the source so that when we specify the drives in the
-- ModuleBody the types enforce that connected wires have the same SignalType at both
-- ends
inductive Source
  {nChildren : Nat}
  (ports : ModulePorts)
  (childPorts : ChildPorts nChildren)
  : SignalType → Type
| input (inputKey : ports.InputKey)
  : Source ports childPorts (ports.inputTypes inputKey)
| childOutput (childKey : Fin nChildren) (outputKey : (childPorts childKey).OutputKey)
  : Source ports childPorts ((childPorts childKey).outputTypes outputKey)

--def Source.getType
--    (_ : Source ports childPorts signalType) : SignalType :=
--  signalType

structure ModuleBody where
  ports : ModulePorts
  nChildren : Nat
  childPorts : ChildPorts nChildren
  childInputDrivers :
    (childKey : Fin nChildren) →
    (childInputKey : (childPorts childKey).InputKey) →
    Source ports childPorts ((childPorts childKey).inputTypes childInputKey)
  outputDrivers :
    (outputKey : ports.OutputKey) →
    Source ports childPorts (ports.outputTypes outputKey)

def ModuleBody.ChildKey (body : ModuleBody) := Fin body.nChildren
def ModuleBody.ChildValues (body : ModuleBody) :=
  (childKey : body.ChildKey) → (body.childPorts childKey).Values

def getSourceValue
    {body : ModuleBody}
    (values : body.ports.Values)
    (childValues : body.ChildValues)
    (src : Source body.ports body.childPorts signalType) : signalType.Denote :=
  match src with
  | .input inputKey => values.inputs inputKey
  | .childOutput childKey childOutputKey => (childValues childKey).outputs childOutputKey

-- All the ports values for the input and outputs of the parent and children along
-- with a `valid` proposition to say they are consistent with the wiring.
structure BodyValues (body : ModuleBody) where
  values : body.ports.Values
  childValues : body.ChildValues
  valid : (
      ∀ outputKey,
        values.outputs outputKey =
        getSourceValue values childValues (body.outputDrivers outputKey)
    ) ∧ (
      ∀ childKey childInputKey,
        (childValues childKey).inputs childInputKey =
        getSourceValue values childValues (body.childInputDrivers childKey childInputKey)
    )

abbrev BodyTrace (body : ModuleBody) := List (BodyValues body)

abbrev ChildSpecs (body : ModuleBody) := (childKey : body.ChildKey) → Spec (body.childPorts childKey)
abbrev ChildDepSets (body : ModuleBody) := (childKey : body.ChildKey) → DepSets (body.childPorts childKey)

def BodyTrace.trace (trace : BodyTrace body): PortTrace body.ports := trace.map BodyValues.values
def BodyTrace.childTrace (trace : BodyTrace body) (childKey : body.ChildKey)
  : PortTrace (body.childPorts childKey) := trace.map fun x => x.childValues childKey

def BodyTraceMatchesSpec {body : ModuleBody} (spec : Spec body.ports) (trace : BodyTrace body) : Prop :=
  spec.traceCondition (BodyTrace.trace trace)

def BodyTraceMatchesChildSpecs
    {body : ModuleBody}
    (childSpecs : ChildSpecs body)
    (trace : BodyTrace body) : Prop :=
  ∀ childKey,
    (childSpecs childKey).traceCondition (BodyTrace.childTrace trace childKey)

inductive BodyNode (body : ModuleBody)
  | input (inputKey : body.ports.InputKey)
  | output (outputKey : body.ports.OutputKey)
  | childInput (childKey : body.ChildKey) (childInputKey : (body.childPorts childKey).InputKey)
  | childOutput (childKey : body.ChildKey) (childOutputKey : (body.childPorts childKey).OutputKey)

def BodyNode.ofSource {body : ModuleBody}
    (src : Source body.ports body.childPorts signalType) : BodyNode body :=
  match src with
  | .input inputKey => .input inputKey
  | .childOutput childKey childOutputKey => .childOutput childKey childOutputKey

-- We can construct one of these to prove that there is a direct connection from one
-- BodyNode to another.
inductive DirectlyDependsOn {body : ModuleBody} (childDeps : ChildDepSets body) :
    BodyNode body → BodyNode body → Prop where
  | output (outputKey : body.ports.OutputKey)
    : DirectlyDependsOn childDeps
      (.output outputKey) (BodyNode.ofSource (body.outputDrivers outputKey))
  | childInput (childKey : body.ChildKey) (childInputKey : (body.childPorts childKey).InputKey)
    : DirectlyDependsOn childDeps
      (.childInput childKey childInputKey)
      (BodyNode.ofSource (body.childInputDrivers childKey childInputKey))
  | childOutput (childKey : body.ChildKey) (childOutputKey : (body.childPorts childKey).OutputKey)
      (childInputKey : (body.childPorts childKey).InputKey)
      (depends : childInputKey ∈ ((childDeps childKey).requires childOutputKey))
    : DirectlyDependsOn childDeps
      (.childOutput childKey childOutputKey)
      (.childInput  childKey childInputKey)

-- We show that there is a path from one BodyNode to another.
inductive PathBetweenNodes
    {body : ModuleBody}
    (childDeps : ChildDepSets body)
    (startNode : BodyNode body) : BodyNode body → Prop where
  | nil : PathBetweenNodes childDeps startNode startNode
  | cons {nodeA : BodyNode body} {nodeB : BodyNode body}
      (step : DirectlyDependsOn childDeps nodeA nodeB)
      (path : PathBetweenNodes childDeps startNode nodeA)
    : PathBetweenNodes childDeps startNode nodeB

def ChildDepSets.ofChildSpecs
    {body : ModuleBody}
    (childSpecs : ChildSpecs body)
    (childKey : body.ChildKey): DepSets (body.childPorts childKey) :=
  (childSpecs childKey).deps

def DepsSound {body : ModuleBody}
    (spec : Spec body.ports) (childSpecs : ChildSpecs body): Prop :=
  ∀ outputKey inputKey,
    PathBetweenNodes (ChildDepSets.ofChildSpecs childSpecs)
      (.output outputKey) (.input inputKey) →
    inputKey ∈ (spec.deps.requires outputKey)

def ChildSpecs.HasSolution {body : ModuleBody}
    (childSpecs : ChildSpecs body): Prop :=
  ∀ inputs : List body.ports.InputValues,
    ∃ trace, trace.trace.inputs = inputs ∧
             BodyTraceMatchesChildSpecs childSpecs trace

def ChildSpecsImplySpec {body : ModuleBody}
    (spec : Spec body.ports) (childSpecs : ChildSpecs body): Prop :=
  ∀ trace,
    BodyTraceMatchesChildSpecs childSpecs trace →
    BodyTraceMatchesSpec spec trace

abbrev ModuleBodyCertValid {body : ModuleBody}
    (spec : Spec body.ports) (childSpecs : ChildSpecs body) : Prop :=
  DepsSound spec childSpecs ∧
  childSpecs.HasSolution ∧
  ChildSpecsImplySpec spec childSpecs

structure ModuleBodyCert (body : ModuleBody) where
  spec : Spec body.ports
  childSpecs : ChildSpecs body
  valid : ModuleBodyCertValid spec childSpecs

end Silean2.Foundations
