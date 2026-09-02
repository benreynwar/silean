import Silean.Composition.Reduction
import Silean.Naming.ModuleNaming

namespace Silean.Composition.Reduction.Naming

open Silean Silean.Naming

/-! Presentation names for reduction trees are kept separate from their
generic structural construction and certification. -/

def ports (signalType : SignalType) (tree : Tree) :
    ModulePortsNaming (Reduction.ports signalType tree) where
  inputs := ⟨fun | .leaf index => .indexed "input" index.val⟩
  outputs := ⟨fun | .output => "result"⟩

private def treeParameters : Tree → List ModuleParameter
  | .empty => [.natural 0]
  | .leaf => [.natural 1]
  | .node left right =>
      .natural 2 :: treeParameters left ++ treeParameters right

def naming (family : String)
    (binary : BinaryImplementation signalType operation)
    (identityModule : IdentityImplementation signalType identity)
    (binaryNaming : ModuleNaming binary.moduleStructure)
    (identityNaming : ModuleNaming identityModule.moduleStructure) :
    (tree : Tree) → ModuleNaming
      (Reduction.moduleStructure binary identityModule tree)
  | .empty => .composite
      ⟨family, "empty", .shape signalType :: treeParameters .empty⟩
      (ports signalType .empty)
      (fun | .identity => "identity")
      (fun | .identity => identityNaming)
  | .leaf => .composite
      ⟨family, "leaf", .shape signalType :: treeParameters .leaf⟩
      (ports signalType .leaf)
      (fun impossible => nomatch impossible)
      (fun impossible => nomatch impossible)
  | .node left right => .composite
      ⟨family, "node", .shape signalType :: treeParameters (.node left right)⟩
      (ports signalType (.node left right))
      (fun
        | .left => "left"
        | .right => "right"
        | .combine => "combine")
      (fun
        | .left => naming family binary identityModule binaryNaming identityNaming left
        | .right => naming family binary identityModule binaryNaming identityNaming right
        | .combine => binaryNaming)

end Silean.Composition.Reduction.Naming
