import Silean.Foundation.SignalLayout
import Silean.Composition.SignalAdapter
import Silean.Composition.SignalAdapterImplementation
import Silean.Composition.SignalLogic
import Silean.Composition.LeafwiseComposition
import Silean.Composition.BinaryLeafwise
import Silean.Composition.Reduction
import Silean.Composition.FifoSerialComposition
import Silean.Composition.FifoSerialCertification
import Silean.Composition.FifoSerialRefinement

/-! # Reusable composition mechanisms

This aggregate exports generic ways to construct and certify hardware from
other modules. It includes aggregate signal adapters, leafwise and binary
composition, balanced reduction, and serial FIFO composition. These files own
patterns parameterized by signal shapes, operations, or child contracts;
concrete reusable components belong under `Silean.Modules`.
-/
