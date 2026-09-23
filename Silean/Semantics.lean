import Silean.Semantics.Trace
import Silean.Semantics.BoundaryTrace
import Silean.Semantics.FixedLatency
import Silean.Semantics.FramedLatency
import Silean.Semantics.DelayLine
import Silean.Semantics.StructuralEquations
import Silean.Semantics.ModuleBodyTrace
import Silean.Semantics.StructuralDependency
import Silean.Semantics.StructuralExecution
import Silean.Semantics.StructuralObservation

/-! # Contract-independent semantics

This aggregate gives `ModuleStructure` its mathematical behavior independently
of contracts and authoring syntax. `StructuralEquations` defines simultaneous
one-cycle solutions, `StructuralDependency` expresses when those solutions are
unique, and `StructuralExecution` turns solutions into transitions and finite
`Trace`s. No definition here selects an evaluator or stores an execution order
in the hardware structure.
-/
