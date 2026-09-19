import Lean

/-! The named simp set used by circuit-description correspondence proofs.

This declaration lives in its own imported module because Lean makes the
generated attribute syntax available only after the declaring module has been
compiled. Definitions that participate in builder normalization add
themselves to this set in their owning files.
-/

register_simp_attr circuit_description
