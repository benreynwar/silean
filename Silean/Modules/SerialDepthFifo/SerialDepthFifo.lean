import Silean.Modules.OneEntryFifo.OneEntryFifoCycleBehavior
import Silean.Composition.FifoSerialComposition

namespace Silean.Modules.SerialDepthFifo

open Silean
open Contracts.Fifo.Cycle
open OneEntryFifo

/-! A positive-depth FIFO assembled by connecting fall-through one-entry FIFOs
in series. The public `depth` is the total number of entries. -/

/-! `additionalDepth` counts entries after the required first entry.  It is an
internal recursion index; the public API below takes the FIFO's actual positive
depth. -/

private def moduleStructureFromAdditional (signalType : SignalType) :
    (additionalDepth : Nat) → ModuleStructure (Silean.Interfaces.Fifo.ports signalType)
  | 0 => OneEntryFifo.moduleStructure signalType
  | additionalDepth + 1 =>
      Composition.FifoSerial.moduleStructure signalType
        (OneEntryFifo.moduleStructure signalType)
        (moduleStructureFromAdditional signalType additionalDepth)

noncomputable def certifiedCycleBehaviorFromAdditional (signalType : SignalType) :
    (additionalDepth : Nat) → CertifiedCycleBehavior signalType
  | 0 => oneEntryCertified signalType
  | additionalDepth + 1 =>
      Composition.FifoSerial.certifiedCycleBehavior (oneEntryCertified signalType)
        (certifiedCycleBehaviorFromAdditional signalType additionalDepth)

private def cycleBehaviorFromAdditional (signalType : SignalType) :
    (additionalDepth : Nat) → CycleBehavior signalType
  | 0 => oneEntryCycleBehavior signalType
  | additionalDepth + 1 =>
      (oneEntryCycleBehavior signalType).serial
        (cycleBehaviorFromAdditional signalType additionalDepth)

@[simp] theorem certifiedCycleBehaviorFromAdditional_behavior
    (signalType : SignalType) (additionalDepth : Nat) :
    (certifiedCycleBehaviorFromAdditional signalType additionalDepth).cycleBehavior =
      cycleBehaviorFromAdditional signalType additionalDepth := by
  induction additionalDepth with
  | zero => rfl
  | succ additionalDepth induction =>
      simp only [certifiedCycleBehaviorFromAdditional, cycleBehaviorFromAdditional,
        Composition.FifoSerial.certifiedCycleBehavior, oneEntryCertified]
      rw [induction]

@[simp] theorem certifiedCycleBehaviorFromAdditional_moduleStructure
    (signalType : SignalType) (additionalDepth : Nat) :
    (certifiedCycleBehaviorFromAdditional signalType additionalDepth).moduleStructure =
      moduleStructureFromAdditional signalType additionalDepth := by
  induction additionalDepth with
  | zero => rfl
  | succ additionalDepth induction =>
      simp only [certifiedCycleBehaviorFromAdditional, moduleStructureFromAdditional,
        Composition.FifoSerial.certifiedCycleBehavior, oneEntryCertified]
      rw [induction]

def additionalDepth (depth : Nat) : Nat := depth - 1

theorem additionalDepth_eq {depth : Nat} (positive : 0 < depth) :
    additionalDepth depth + 1 = depth := by
  unfold additionalDepth
  omega

def moduleStructure (signalType : SignalType) (depth : Nat) (_positive : 0 < depth) :
    ModuleStructure (Silean.Interfaces.Fifo.ports signalType) :=
  moduleStructureFromAdditional signalType (additionalDepth depth)

private noncomputable def certifiedCycleBehavior (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) : CertifiedCycleBehavior signalType :=
  let assembled := certifiedCycleBehaviorFromAdditional signalType (additionalDepth depth)
  { cycleBehavior := cycleBehaviorFromAdditional signalType (additionalDepth depth)
    moduleStructure := moduleStructure signalType depth positive
    certification := (assembled.certification.transportStructure
      (by
        simp only [moduleStructure]
        exact certifiedCycleBehaviorFromAdditional_moduleStructure signalType
          (additionalDepth depth))).transportContract
      (congrArg CycleBehavior.cycleContract
        (certifiedCycleBehaviorFromAdditional_behavior signalType (additionalDepth depth))) }

def cycleBehavior (signalType : SignalType) (depth : Nat) (_positive : 0 < depth) :
    CycleBehavior signalType :=
  cycleBehaviorFromAdditional signalType (additionalDepth depth)

@[simp] theorem cycleBehavior_one (signalType : SignalType)
    (positive : 0 < 1) :
    cycleBehavior signalType 1 positive = oneEntryCycleBehavior signalType := rfl

@[simp] theorem cycleBehavior_step (signalType : SignalType)
    (additionalDepth : Nat) (positive : 0 < additionalDepth + 2) :
    cycleBehavior signalType (additionalDepth + 2) positive =
      (oneEntryCycleBehavior signalType).serial
        (cycleBehavior signalType (additionalDepth + 1) (by omega)) := by
  simp only [cycleBehavior, SerialDepthFifo.additionalDepth, Nat.add_sub_cancel]
  rfl

def cycleContract (signalType : SignalType) (depth : Nat) (positive : 0 < depth) :
    Contracts.Cycle.ModuleCycleContract (Silean.Interfaces.Fifo.ports signalType) :=
  (cycleBehavior signalType depth positive).cycleContract

noncomputable def certification (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    Contracts.Cycle.ModuleCycleCertification (moduleStructure signalType depth positive)
      (cycleContract signalType depth positive) :=
  (certifiedCycleBehavior signalType depth positive).certification

noncomputable def certified (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    Contracts.Cycle.ModuleCycleCertified (Silean.Interfaces.Fifo.ports signalType) :=
  (certification signalType depth positive).bundle

@[simp] theorem certified_moduleStructure (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    (certified signalType depth positive).moduleStructure =
      moduleStructure signalType depth positive := rfl

@[simp] theorem certified_cycleContract (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    (certified signalType depth positive).cycleContract =
      cycleContract signalType depth positive := rfl

end Silean.Modules.SerialDepthFifo

namespace Silean.Modules.SerialDepthFifo.Naming

open Silean Silean.Naming

def namingFromAdditional (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) :
    (additionalDepth : Nat) →
      ModuleNaming (Modules.SerialDepthFifo.moduleStructureFromAdditional signalType additionalDepth)
  | 0 => Modules.OneEntryFifo.Naming.namingWith signalType typeNaming
  | additionalDepth + 1 =>
      Composition.FifoSerial.Naming.serialNamingWith signalType typeNaming (additionalDepth + 2)
        (Modules.OneEntryFifo.Naming.namingWith signalType typeNaming)
        (namingFromAdditional signalType typeNaming additionalDepth)

def depthNamingWith (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType)
    (depth : Nat) (positive : 0 < depth) :
    ModuleNaming (Modules.SerialDepthFifo.moduleStructure signalType depth positive) :=
  namingFromAdditional signalType typeNaming (Modules.SerialDepthFifo.additionalDepth depth)

def depthNaming (signalType : SignalType) (depth : Nat) (positive : 0 < depth) :
    ModuleNaming (Modules.SerialDepthFifo.moduleStructure signalType depth positive) :=
  depthNamingWith signalType (.positional signalType) depth positive

end Silean.Modules.SerialDepthFifo.Naming
