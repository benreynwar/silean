import Silean.Authoring.CircuitDescription
import Silean.Modules.OneEntryFifo.OneEntryFifo
import Silean.Naming.FifoSerialNaming

namespace Silean.Modules.SerialDepthFifo

open Silean
open Contracts.Fifo.Cycle
open OneEntryFifo

/-! # Serial-depth FIFO

A positive-depth FIFO assembled by connecting fall-through one-entry FIFOs in
series. The public `depth` is the total number of entries.

This module deliberately keeps its recursive `ModuleStructure` as the primary
hardware definition instead of adding a `CircuitDescription.Builder` version.
The hierarchy itself changes with `depth`, and each recursive step is exactly
the already-certified generic `FifoSerial` composition. A second handwritten
builder recursion would duplicate that programmatic construction without
making the hardware easier to understand.
-/

/-! `additionalDepth` counts entries after the required first entry. It is an
internal recursion index; the public API below takes the FIFO's actual positive
depth. Ordinary Lean recursion is intentional here because each step wraps a
smaller, differently typed hierarchy rather than declaring a fixed child set. -/

def moduleStructureFromAdditional (signalType : SignalType)
    :
    (additionalDepth : Nat) → ModuleStructure (Silean.Interfaces.Fifo.ports signalType)
  | 0 => OneEntryFifo.moduleStructure signalType
  | additionalDepth + 1 =>
      Composition.FifoSerial.moduleStructure signalType
        (OneEntryFifo.moduleStructure signalType)
        (moduleStructureFromAdditional signalType additionalDepth)

def cycleBehaviorFromAdditional (signalType : SignalType) :
    (additionalDepth : Nat) → CycleBehavior signalType
  | 0 => OneEntryFifo.cycleBehavior signalType
  | additionalDepth + 1 =>
      (OneEntryFifo.cycleBehavior signalType).serial
        (cycleBehaviorFromAdditional signalType additionalDepth)

def additionalDepth (depth : Nat) : Nat := depth - 1

theorem additionalDepth_eq {depth : Nat} (positive : 0 < depth) :
    additionalDepth depth + 1 = depth := by
  unfold additionalDepth
  omega

def moduleStructure (signalType : SignalType)
    (depth : Nat) (_positive : 0 < depth) :
    ModuleStructure (Silean.Interfaces.Fifo.ports signalType) :=
  moduleStructureFromAdditional signalType (additionalDepth depth)

def cycleBehavior (signalType : SignalType) (depth : Nat) (_positive : 0 < depth) :
    CycleBehavior signalType :=
  cycleBehaviorFromAdditional signalType (additionalDepth depth)

@[simp] theorem cycleBehavior_one (signalType : SignalType)
    (positive : 0 < 1) :
    cycleBehavior signalType 1 positive = OneEntryFifo.cycleBehavior signalType := rfl

@[simp] theorem cycleBehavior_step (signalType : SignalType)
    (additionalDepth : Nat) (positive : 0 < additionalDepth + 2) :
    cycleBehavior signalType (additionalDepth + 2) positive =
      (OneEntryFifo.cycleBehavior signalType).serial
        (cycleBehavior signalType (additionalDepth + 1) (by omega)) := by
  simp only [cycleBehavior, SerialDepthFifo.additionalDepth, Nat.add_sub_cancel]
  rfl

def cycleContract (signalType : SignalType) (depth : Nat) (positive : 0 < depth) :
    Contracts.Cycle.ModuleCycleContract (Silean.Interfaces.Fifo.ports signalType) :=
  (cycleBehavior signalType depth positive).cycleContract

end Silean.Modules.SerialDepthFifo

namespace Silean.Modules.SerialDepthFifo.Naming

open Silean Silean.Naming

def namingFromAdditional (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) :
    (additionalDepth : Nat) →
      ModuleNaming (Modules.SerialDepthFifo.moduleStructureFromAdditional signalType additionalDepth)
  | 0 => Modules.OneEntryFifo.namingWith signalType typeNaming
  | additionalDepth + 1 =>
      Composition.FifoSerial.Naming.serialNamingWith signalType typeNaming (additionalDepth + 2)
        (Modules.OneEntryFifo.namingWith signalType typeNaming)
        (namingFromAdditional signalType typeNaming additionalDepth)

def depthNamingWith (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType)
    (depth : Nat) (positive : 0 < depth) :
    ModuleNaming (Modules.SerialDepthFifo.moduleStructure signalType depth positive) :=
  namingFromAdditional signalType typeNaming
    (Modules.SerialDepthFifo.additionalDepth depth)

def depthNaming (signalType : SignalType) (depth : Nat) (positive : 0 < depth) :
    ModuleNaming (Modules.SerialDepthFifo.moduleStructure signalType depth positive) :=
  depthNamingWith signalType (.positional signalType) depth positive

end Silean.Modules.SerialDepthFifo.Naming

namespace Silean.Modules.SerialDepthFifo

open Silean Silean.Naming
open Silean.Authoring.CircuitDescription

/-- The complete recursively assembled design with authored payload names. -/
@[reducible] def designWith (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType)
    (depth : Nat) (positive : 0 < depth) : NamedModule :=
  ⟨Silean.Interfaces.Fifo.ports signalType,
    moduleStructure signalType depth positive,
    Naming.depthNamingWith signalType typeNaming depth positive⟩

/-- The complete recursively assembled design with positional payload names. -/
@[reducible] def design (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) : NamedModule :=
  designWith signalType (.positional signalType) depth positive

/-! ## Placement -/

/-- Place a positive-depth serial FIFO under a caller-chosen instance name. -/
noncomputable def placeNamed (name : SourceName)
    (depth : Nat) (positive : 0 < depth)
    (inputValid : Net .bit) (inputData : Net signalType)
    (outputReady reset : Net .bit) :
    Builder (OneEntryFifo.PlacedOutputs signalType) := do
  let child ← Authoring.CircuitDescription.placeNamed name
    (design signalType depth positive) fun
      | .inputValid => inputValid
      | .inputData => inputData
      | .outputReady => outputReady
      | .reset => reset
  pure {
    outputValid := child .outputValid
    outputData := child .outputData
    inputReady := child .inputReady }

end Silean.Modules.SerialDepthFifo
