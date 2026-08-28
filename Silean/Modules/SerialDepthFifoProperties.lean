import Silean.Modules.SerialDepthFifo
import Silean.Modules.NoResetFifoExecution
import Silean.Modules.OneEntryFifoProperties

namespace Silean.Modules.SerialDepthFifo.Properties

open Silean.Contracts
open NoResetFifo

abbrev Word (signalType : SignalType) := signalType.Denote

structure CertifiedView (cycleBehavior : CycleBehavior signalType) where
  view : NoResetFifo.View cycleBehavior.state.Values (Word signalType)
  satisfies : NoResetFifo.View.Satisfies view
    (Execution.model cycleBehavior).executes

private def oneEntryView (signalType : SignalType) :
    CertifiedView (oneEntryCycleBehavior signalType) where
  view := OneEntryFifo.Properties.fifoView signalType
  satisfies := OneEntryFifo.Properties.fifoView_satisfies signalType

@[simp] private theorem oneEntryView_capacity (signalType : SignalType) :
    (oneEntryView signalType).view.capacity = 1 := rfl

@[simp] private theorem oneEntryView_readyPropagationLatency (signalType : SignalType) :
    (oneEntryView signalType).view.readyPropagationLatency = 0 := rfl

def CertifiedView.serial {upstream downstream : CycleBehavior signalType}
    (upstreamView : CertifiedView upstream) (downstreamView : CertifiedView downstream) :
    CertifiedView (upstream.serial downstream) := by
  let outerView : NoResetFifo.View
      (upstream.serial downstream).state.Values (Word signalType) :=
    { contents := fun state =>
        downstreamView.view.contents (rightState state) ++
          upstreamView.view.contents (leftState state)
      capacity := upstreamView.view.capacity + downstreamView.view.capacity
      readyPropagationLatency := upstreamView.view.readyPropagationLatency +
        downstreamView.view.readyPropagationLatency
      contents_bounded := by
        intro state
        simp only [List.length_append]
        have upstreamBound := upstreamView.view.contents_bounded (leftState state)
        have downstreamBound := downstreamView.view.contents_bounded (rightState state)
        omega }
  let constructor : NoResetFifo.View.Execution.Constructor
      outerView upstreamView.view downstreamView.view
      (Execution.model (upstream.serial downstream))
      (Execution.model upstream) (Execution.model downstream) :=
    { serial := Execution.serial upstream downstream
      contents := fun _ => rfl }
  exact
    { view := outerView
      satisfies := constructor.satisfies rfl rfl upstreamView.satisfies
        downstreamView.satisfies }

@[simp] theorem CertifiedView.serial_capacity
    {upstream downstream : CycleBehavior signalType}
    (upstreamView : CertifiedView upstream) (downstreamView : CertifiedView downstream) :
    (upstreamView.serial downstreamView).view.capacity =
      upstreamView.view.capacity + downstreamView.view.capacity := rfl

@[simp] theorem CertifiedView.serial_readyPropagationLatency
    {upstream downstream : CycleBehavior signalType}
    (upstreamView : CertifiedView upstream) (downstreamView : CertifiedView downstream) :
    (upstreamView.serial downstreamView).view.readyPropagationLatency =
      upstreamView.view.readyPropagationLatency +
        downstreamView.view.readyPropagationLatency := rfl

private def CertifiedView.cast {left right : CycleBehavior signalType}
    (equal : left = right) (value : CertifiedView left) : CertifiedView right :=
  equal ▸ value

@[simp] private theorem CertifiedView.cast_capacity
    {left right : CycleBehavior signalType} (equal : left = right)
    (value : CertifiedView left) :
    (value.cast equal).view.capacity = value.view.capacity := by
  subst right
  rfl

@[simp] private theorem CertifiedView.cast_readyPropagationLatency
    {left right : CycleBehavior signalType} (equal : left = right)
    (value : CertifiedView left) :
    (value.cast equal).view.readyPropagationLatency =
      value.view.readyPropagationLatency := by
  subst right
  rfl

private structure DepthView (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) where
  certified : CertifiedView (cycleBehavior signalType depth positive)
  capacity : certified.view.capacity = depth
  readyPropagationLatency : certified.view.readyPropagationLatency = 0

private noncomputable def depthView (signalType : SignalType) :
    (depth : Nat) → (positive : 0 < depth) → DepthView signalType depth positive
  | 0, positive => False.elim (by omega)
  | 1, positive =>
      let certified :=
        (oneEntryView signalType).cast (cycleBehavior_one signalType positive).symm
      { certified
        capacity := by simp [certified]
        readyPropagationLatency := by simp [certified] }
  | additionalDepth + 2, positive =>
      let downstream := depthView signalType (additionalDepth + 1) (by omega)
      let certified := ((oneEntryView signalType).serial downstream.certified).cast
        (cycleBehavior_step signalType additionalDepth positive).symm
      { certified
        capacity := by
          simp only [certified, CertifiedView.cast_capacity,
            CertifiedView.serial_capacity, oneEntryView_capacity,
            downstream.capacity]
          omega
        readyPropagationLatency := by
          simp only [certified, CertifiedView.cast_readyPropagationLatency,
            CertifiedView.serial_readyPropagationLatency,
            oneEntryView_readyPropagationLatency,
            downstream.readyPropagationLatency, Nat.zero_add] }

noncomputable def certifiedView (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    CertifiedView (cycleBehavior signalType depth positive) :=
  (depthView signalType depth positive).certified

@[simp] theorem capacity_eq_depth (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    (certifiedView signalType depth positive).view.capacity = depth :=
  (depthView signalType depth positive).capacity

@[simp] theorem readyPropagationLatency_eq_zero (signalType : SignalType)
    (depth : Nat) (positive : 0 < depth) :
    (certifiedView signalType depth positive).view.readyPropagationLatency = 0 :=
  (depthView signalType depth positive).readyPropagationLatency

end Silean.Modules.SerialDepthFifo.Properties
