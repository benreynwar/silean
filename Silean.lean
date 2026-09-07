import Silean.Foundation
import Silean.Interfaces
import Silean.Primitives
import Silean.Structure
import Silean.Composition
import Silean.Semantics
import Silean.Contracts
import Silean.Modules
import Silean.Naming
import Silean.Authoring
import Silean.FIRRTL

/-! # Silean

This is the complete public import for Silean's hardware vocabulary,
structure, semantics, contracts, reusable modules, authoring commands, naming,
and FIRRTL backend. Internal files generally import the narrow aggregate or
source module they need; applications may import `Silean` for the full API.
-/
