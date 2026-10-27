import Silean2.Foundations.SignalTypeH

namespace Silean2.Foundations

abbrev PortTypes (nPorts : Nat) := Fin nPorts → SignalType
abbrev PortValues {nPorts : Nat} (portTypes : PortTypes nPorts) :=
  (portIndex : Fin nPorts) → (portTypes portIndex).Denote

instance {nPorts : Nat} : DecidableEq (PortTypes nPorts) := by
  intros a b
  by_cases h : ∀ i, a i = b i
  · apply isTrue
    funext i
    exact h i
  · apply isFalse
    intro functionsEqual
    apply h
    intro i
    rw [functionsEqual]

structure ModulePorts where
  nInputs : Nat
  nOutputs : Nat
  inputTypes : PortTypes nInputs
  outputTypes : PortTypes nOutputs
  deriving DecidableEq

abbrev ModulePorts.InputKey (ports : ModulePorts) := Fin ports.nInputs
abbrev ModulePorts.OutputKey (ports : ModulePorts) := Fin ports.nOutputs
abbrev ModulePorts.InputValues (ports : ModulePorts) := PortValues ports.inputTypes
abbrev ModulePorts.OutputValues (ports : ModulePorts) := PortValues ports.outputTypes

structure BoundaryValues (ports : ModulePorts) where
  inputs : ports.InputValues
  outputs : ports.OutputValues

abbrev ModulePorts.Values (ports : ModulePorts) := BoundaryValues ports

abbrev ModulePorts.Function (ports : ModulePorts) := ports.InputValues → ports.OutputValues

-- Represents that a set of output ports may be combinatorially dependent
-- on a set of input ports.
-- This is used for reasoning about the creation of cycles.
structure DepSet (ports : ModulePorts) where
  requires : List ports.InputKey
  provides : List ports.OutputKey

structure DepSets (ports : ModulePorts) where
  nDepSets : Nat
  depsets : Fin nDepSets → DepSet ports
  outputDepSetKey : ports.OutputKey → Fin nDepSets
  valid : ∀ outputKey : ports.OutputKey,
    let depSetKey := outputDepSetKey outputKey
    outputKey ∈ (depsets depSetKey).provides ∧
    ∀ otherDepSetKey, otherDepSetKey ≠ depSetKey → outputKey ∉ (depsets otherDepSetKey).provides

def DepSets.requires
  (deps : DepSets ports) (outputKey : ports.OutputKey)
  : List ports.InputKey :=
  (deps.depsets (deps.outputDepSetKey outputKey)).requires


-- For when all outputs depend on all inputs

abbrev ModulePorts.allInputKeys (ports : ModulePorts) : List ports.InputKey :=
  List.finRange ports.nInputs
abbrev ModulePorts.allOutputKeys (ports : ModulePorts) : List ports.OutputKey :=
  List.finRange ports.nOutputs

abbrev DepSet.whole (ports : ModulePorts) : DepSet ports :=
  {
    requires := ports.allInputKeys
    provides := ports.allOutputKeys
  }

abbrev DepSets.whole (ports : ModulePorts) : DepSets ports :=
  {
    nDepSets := 1
    depsets := fun _ => DepSet.whole ports
    outputDepSetKey := fun _ => 0
    valid := by simp
  }

-- The requires of any output are all inputs
theorem wholeDepSetsRequireAllInputs
    {ports : ModulePorts} (outputKey : ports.OutputKey) (inputKey : ports.InputKey):
  inputKey ∈ ((DepSets.whole ports).requires outputKey) := by
    simp [DepSets.requires]

end Silean2.Foundations
