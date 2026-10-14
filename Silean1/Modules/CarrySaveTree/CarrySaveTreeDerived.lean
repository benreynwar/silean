import Silean.Modules.CarrySaveTree.Internal.CarrySaveTreeVerification

/-! Public carry-save-tree declarations backed by the recursive structure. -/

namespace Silean.Modules.CarrySaveTree

open Silean
open Authoring.CircuitDescription

/-- Place a recursive carry-save reduction from a collection of operands to
two fixed-width results. -/
noncomputable def place
    (operands : Net (.vector operandCount (.vector width .bit))) :
    Builder (ports.OutputNets width operandCount) :=
  ports.placeIndexed width operandCount "carry_save_tree"
    (moduleStructure width operandCount) (naming width operandCount) operands

attribute [circuit_description] place

/-- The recursive hierarchy has exactly one structural solution for every
boundary input and physical state, independently of its relational contract. -/
theorem structuralCertification (width operandCount : Nat) :
    ModuleStructuralCertification (moduleStructure width operandCount) :=
  Internal.structuralCertification width operandCount

/-- Every realizable tree preserves the input total and uses the natural
pass-through representation for collections of at most two operands. -/
theorem contract_of_realization (width operandCount : Nat)
    {step : (moduleStructure width operandCount).Step}
    (realizes : (moduleStructure width operandCount).Realizes step) :
    contract width operandCount step.inputs step.outputs :=
  Internal.contract_of_realization width operandCount realizes

end Silean.Modules.CarrySaveTree
