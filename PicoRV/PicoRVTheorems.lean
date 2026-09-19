import PicoRV.Internal.PicoRVVerification

/-! # PicoRV top-level theorems

This is the supported proof interface for the complete processor hierarchy.
The child certifications and dependency schedule remain under `Internal/`.
-/

namespace PicoRV.PicoRV

open Silean

/-- The top-level structural equations have at most one solution for fixed
boundary inputs and physical state. -/
theorem hasAtMostOneSolution : moduleStructure.HasAtMostOneSolution :=
  Internal.hasAtMostOneSolution

/-- The top-level structural equations have a solution for every boundary
input and physical state. -/
theorem hasSolution : moduleStructure.HasSolution :=
  Internal.hasSolution

/-- The top-level structural equations have exactly one solution. -/
theorem hasExactlyOneSolution : moduleStructure.HasExactlyOneSolution :=
  ⟨hasSolution, hasAtMostOneSolution⟩

/-- The complete processor hierarchy and all descendants are concrete. -/
theorem moduleStructure_hasNoBlackboxes : moduleStructure.HasNoBlackboxes := by
  native_decide

end PicoRV.PicoRV
