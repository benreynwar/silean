import Silean2.Modules.SerialFifo

namespace Silean2.Modules.SerialDepthFifo

open Silean2
open NoResetFifo

/-! `additionalDepth` counts entries after the required first entry.  It is an
internal recursion index; the public API below takes the FIFO's actual positive
depth. -/

private def moduleStructureFromAdditional (signalType : SignalType) :
    (additionalDepth : Nat) → ModuleStructure (NoResetFifo.ports signalType)
  | 0 => OneEntryFifo.moduleStructure signalType
  | additionalDepth + 1 =>
      SerialFifo.moduleStructure signalType
        (OneEntryFifo.moduleStructure signalType)
        (moduleStructureFromAdditional signalType additionalDepth)

private noncomputable def certifiedFromAdditional (signalType : SignalType) :
    (additionalDepth : Nat) → CertifiedCycleBehavior signalType
  | 0 => oneEntryCertified signalType
  | additionalDepth + 1 =>
      SerialFifo.certifiedCycleBehavior (oneEntryCertified signalType)
        (certifiedFromAdditional signalType additionalDepth)

private def cycleBehaviorFromAdditional (signalType : SignalType) :
    (additionalDepth : Nat) → CycleBehavior signalType
  | 0 => oneEntryCycleBehavior signalType
  | additionalDepth + 1 =>
      (oneEntryCycleBehavior signalType).serial
        (cycleBehaviorFromAdditional signalType additionalDepth)

@[simp] private theorem certifiedFromAdditional_behavior
    (signalType : SignalType) (additionalDepth : Nat) :
    (certifiedFromAdditional signalType additionalDepth).cycleBehavior =
      cycleBehaviorFromAdditional signalType additionalDepth := by
  induction additionalDepth with
  | zero => rfl
  | succ additionalDepth induction =>
      simp only [certifiedFromAdditional, cycleBehaviorFromAdditional,
        SerialFifo.certifiedCycleBehavior, oneEntryCertified]
      rw [induction]

@[simp] private theorem certifiedFromAdditional_moduleStructure
    (signalType : SignalType) (additionalDepth : Nat) :
    (certifiedFromAdditional signalType additionalDepth).moduleStructure =
      moduleStructureFromAdditional signalType additionalDepth := by
  induction additionalDepth with
  | zero => rfl
  | succ additionalDepth induction =>
      simp only [certifiedFromAdditional, moduleStructureFromAdditional,
        SerialFifo.certifiedCycleBehavior, oneEntryCertified]
      rw [induction]

private def additionalDepth (depth : Nat) : Nat := depth - 1

private theorem additionalDepth_eq {depth : Nat} (positive : 0 < depth) :
    additionalDepth depth + 1 = depth := by
  unfold additionalDepth
  omega

def moduleStructure (signalType : SignalType) (depth : Nat) (_positive : 0 < depth) :
    ModuleStructure (NoResetFifo.ports signalType) :=
  moduleStructureFromAdditional signalType (additionalDepth depth)

private noncomputable def certifiedCycleBehavior (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) : CertifiedCycleBehavior signalType :=
  let assembled := certifiedFromAdditional signalType (additionalDepth depth)
  { cycleBehavior := cycleBehaviorFromAdditional signalType (additionalDepth depth)
    moduleStructure := moduleStructure signalType depth positive
    certification := (assembled.certification.transportStructure
      (by
        simp only [moduleStructure]
        exact certifiedFromAdditional_moduleStructure signalType
          (additionalDepth depth))).transportContract
      (congrArg CycleBehavior.cycleContract
        (certifiedFromAdditional_behavior signalType (additionalDepth depth))) }

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
    ModuleCycleContract (NoResetFifo.ports signalType) :=
  (cycleBehavior signalType depth positive).cycleContract

noncomputable def certification (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    ModuleCycleCertification (moduleStructure signalType depth positive)
      (cycleContract signalType depth positive) :=
  (certifiedCycleBehavior signalType depth positive).certification

noncomputable def certified (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    ModuleCycleCertified (NoResetFifo.ports signalType) :=
  (certification signalType depth positive).bundle

@[simp] theorem certified_moduleStructure (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    (certified signalType depth positive).moduleStructure =
      moduleStructure signalType depth positive := rfl

@[simp] theorem certified_cycleContract (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    (certified signalType depth positive).cycleContract =
      cycleContract signalType depth positive := rfl

end Silean2.Modules.SerialDepthFifo

namespace Silean2.Modules.SerialDepthFifo.Naming

open Silean2 Silean2.Naming

def namingFromAdditional (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) :
    (additionalDepth : Nat) →
      ModuleNaming (Modules.SerialDepthFifo.moduleStructureFromAdditional signalType additionalDepth)
  | 0 => Modules.OneEntryFifo.Naming.namingWith signalType typeNaming
  | additionalDepth + 1 =>
      Modules.SerialFifo.Naming.serialNamingWith signalType typeNaming (additionalDepth + 2)
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

end Silean2.Modules.SerialDepthFifo.Naming
