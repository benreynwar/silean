import Silean.Interfaces.ValidReady
import Silean.Interfaces.FifoPorts

/-! # Reusable module interfaces

This aggregate exports typed views of commonly repeated module boundaries.
Interfaces select and interpret signals—for example, recognizing a
valid/ready payload transfer—without asserting the complete behavior of the
module behind them. Protocol guarantees such as ordering, capacity, latency,
and reset behavior belong in contracts.
-/
