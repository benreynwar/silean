import Silean.Primitives.Definitions
import Silean.Primitives.Not
import Silean.Primitives.And
import Silean.Primitives.Or
import Silean.Primitives.Xor
import Silean.Primitives.Eq
import Silean.Primitives.Register
import Silean.Primitives.Constant

/-! # Primitive hardware leaves

This aggregate exports the built-in leaf operations used to terminate a
`ModuleStructure`: Boolean gates, equality, registers, and constants. Each
public primitive combines its direct structural equations with the associated
cycle behavior, certification, and emission naming needed by parent modules.
Larger hierarchies assembled from these leaves belong under `Composition` or
`Modules`.
-/
