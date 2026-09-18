import Silean.Foundation.SignalType
import Silean.Foundation.DeriveEnumeration
import Silean.Foundation.Enumeration
import Silean.Foundation.SignalMap
import Silean.Foundation.SignalLayout
import Silean.Foundation.SignalGroup
import Silean.Foundation.SignalSelection
import Silean.Foundation.ModulePorts
import Silean.Foundation.StructuralState
import Silean.Foundation.BitVector
import Silean.Foundation.CycleStep

/-! # Foundational hardware types

This aggregate exports the name-independent vocabulary used throughout
Silean: signal shapes and values, finite symbolic labels, typed signal maps and
selections, module boundaries, cycle-boundary values, structural state shapes,
and bit-vector utilities. These definitions describe data and interfaces; they
do not define module hierarchy, circuit behavior, or proof schedules.
-/
