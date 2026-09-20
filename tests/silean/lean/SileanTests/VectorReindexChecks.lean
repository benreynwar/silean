import Silean.Modules.VectorReindex.VectorReindexDerived

namespace SileanTests.VectorReindexChecks

open Silean
open Silean.Modules.VectorReindex

def reverseThree : Fin 3 → Fin 3
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 0

example (input : Fin 3 → Nat) :
    apply reverseThree input 0 = input 2 := rfl

example :
    Contracts.Cycle.Implements
      (moduleStructure (.vector 4 .bit) 3 3 reverseThree)
      (cycleContract (.vector 4 .bit) 3 3 reverseThree)
      (certification (.vector 4 .bit) 3 3 reverseThree).stateCorresponds :=
  implements_contract (.vector 4 .bit) 3 3 reverseThree

end SileanTests.VectorReindexChecks
