import Silean.Structure.Primitive
import Silean.Structure.ModuleBody
import Silean.Structure.ModuleStructure

/-! # Hardware structure

This aggregate exports Silean's structural hardware representation. A
`Primitive` is a leaf with local equations, a `ModuleBody` describes one layer
of named child boundaries and typed wiring, and `ModuleStructure` recursively
chooses concrete children to form a complete hierarchy. Structural meaning,
behavioral contracts, and emission naming are defined in later layers.
-/
