import Silean2.Modules.SerialFifo

namespace Silean2.Modules.Fifo

open Silean2

/-! `additionalDepth` counts entries after the required first entry.  It is an
internal recursion index; the public API below takes the FIFO's actual positive
depth. -/

def moduleStructureFromAdditional (signalType : SignalType) :
    (additionalDepth : Nat) → ModuleStructure (OneEntryFifo.ports signalType)
  | 0 => OneEntryFifo.moduleStructure signalType
  | additionalDepth + 1 =>
      SerialFifo.moduleStructure signalType
        (OneEntryFifo.moduleStructure signalType)
        (moduleStructureFromAdditional signalType additionalDepth)

noncomputable def certifiedFromAdditional (signalType : SignalType) :
    (additionalDepth : Nat) → CertifiedBehavior signalType
  | 0 => oneEntryCertified signalType
  | additionalDepth + 1 =>
      SerialFifo.certifiedBehavior (oneEntryCertified signalType)
        (certifiedFromAdditional signalType additionalDepth)

def behaviorFromAdditional (signalType : SignalType) :
    (additionalDepth : Nat) → Behavior signalType
  | 0 => oneEntryBehavior signalType
  | additionalDepth + 1 =>
      (oneEntryBehavior signalType).serial
        (behaviorFromAdditional signalType additionalDepth)

@[simp] theorem certifiedFromAdditional_behavior
    (signalType : SignalType) (additionalDepth : Nat) :
    (certifiedFromAdditional signalType additionalDepth).behavior =
      behaviorFromAdditional signalType additionalDepth := by
  induction additionalDepth with
  | zero => rfl
  | succ additionalDepth induction =>
      simp only [certifiedFromAdditional, behaviorFromAdditional,
        SerialFifo.certifiedBehavior, oneEntryCertified]
      rw [induction]

@[simp] theorem certifiedFromAdditional_moduleStructure
    (signalType : SignalType) (additionalDepth : Nat) :
    (certifiedFromAdditional signalType additionalDepth).moduleStructure =
      moduleStructureFromAdditional signalType additionalDepth := by
  induction additionalDepth with
  | zero => rfl
  | succ additionalDepth induction =>
      simp only [certifiedFromAdditional, moduleStructureFromAdditional,
        SerialFifo.certifiedBehavior, oneEntryCertified]
      rw [induction]

def additionalDepth (depth : Nat) : Nat := depth - 1

theorem additionalDepth_eq {depth : Nat} (positive : 0 < depth) :
    additionalDepth depth + 1 = depth := by
  unfold additionalDepth
  omega

def moduleStructure (signalType : SignalType) (depth : Nat) (_positive : 0 < depth) :
    ModuleStructure (OneEntryFifo.ports signalType) :=
  moduleStructureFromAdditional signalType (additionalDepth depth)

noncomputable def certifiedBehavior (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) : CertifiedBehavior signalType :=
  let assembled := certifiedFromAdditional signalType (additionalDepth depth)
  { behavior := behaviorFromAdditional signalType (additionalDepth depth)
    moduleStructure := moduleStructure signalType depth positive
    certification := (assembled.certification.transportStructure
      (by
        simp only [moduleStructure]
        exact certifiedFromAdditional_moduleStructure signalType
          (additionalDepth depth))).transportContract
      (congrArg Behavior.cycleContract
        (certifiedFromAdditional_behavior signalType (additionalDepth depth))) }

def behavior (signalType : SignalType) (depth : Nat) (_positive : 0 < depth) :
    Behavior signalType :=
  behaviorFromAdditional signalType (additionalDepth depth)

def cycleContract (signalType : SignalType) (depth : Nat) (positive : 0 < depth) :
    ModuleCycleContract (OneEntryFifo.ports signalType) :=
  (behavior signalType depth positive).cycleContract

noncomputable def certification (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    ModuleCycleCertification (moduleStructure signalType depth positive)
      (cycleContract signalType depth positive) :=
  (certifiedBehavior signalType depth positive).certification

noncomputable def certified (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    ModuleCycleCertified (OneEntryFifo.ports signalType) :=
  (certification signalType depth positive).bundle

@[simp] theorem certified_moduleStructure (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    (certified signalType depth positive).moduleStructure =
      moduleStructure signalType depth positive := rfl

@[simp] theorem certified_cycleContract (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    (certified signalType depth positive).cycleContract =
      cycleContract signalType depth positive := rfl

end Silean2.Modules.Fifo

namespace Silean2.Modules.Fifo.Naming

open Silean2 Silean2.Naming

def namingFromAdditional (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType) :
    (additionalDepth : Nat) →
      ModuleNaming (Modules.Fifo.moduleStructureFromAdditional signalType additionalDepth)
  | 0 => Modules.OneEntryFifo.Naming.namingWith signalType typeNaming
  | additionalDepth + 1 =>
      Modules.SerialFifo.Naming.serialNamingWith signalType typeNaming (additionalDepth + 2)
        (Modules.OneEntryFifo.Naming.namingWith signalType typeNaming)
        (namingFromAdditional signalType typeNaming additionalDepth)

def depthNamingWith (signalType : SignalType)
    (typeNaming : SignalTypeNaming signalType)
    (depth : Nat) (positive : 0 < depth) :
    ModuleNaming (Modules.Fifo.moduleStructure signalType depth positive) :=
  namingFromAdditional signalType typeNaming (Modules.Fifo.additionalDepth depth)

def depthNaming (signalType : SignalType) (depth : Nat) (positive : 0 < depth) :
    ModuleNaming (Modules.Fifo.moduleStructure signalType depth positive) :=
  depthNamingWith signalType (.positional signalType) depth positive

end Silean2.Modules.Fifo.Naming
