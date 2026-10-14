import Silean.Naming
import Silean.FIRRTL.Traversal
import Silean.FIRRTL.Render
import Silean.FIRRTL.Emit

/-! # FIRRTL backend

This aggregate exports traversal, validation, rendering, and file emission for
named Silean hierarchies. The backend consumes `ModuleStructure` together with
its separate naming metadata; it does not define circuit semantics or use
behavioral contracts to choose the emitted structure.
-/
