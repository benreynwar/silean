import Silean.Modules.BitMux.BitMuxTheorems
import Silean.Modules.Constant.Constant
import Silean.Modules.All.All
import Silean.Modules.Any.Any
import Silean.Modules.HalfAdder.HalfAdderDerived
import Silean.Modules.FullAdder.FullAdderDerived
import Silean.Modules.Add.AddDerived
import Silean.Modules.BitwiseXor.BitwiseXor
import Silean.Modules.BitwiseAnd.BitwiseAnd
import Silean.Modules.AddSub.AddSubDerived
import Silean.Modules.Increment.IncrementDerived
import Silean.Modules.Register.RegisterDerived
import Silean.Modules.ResetRegister.ResetRegisterDerived
import Silean.Modules.EnabledResetRegister.EnabledResetRegisterDerived
import Silean.Modules.EnabledResetCounter.EnabledResetCounterDerived
import Silean.Modules.Fifo.FifoFifoTheorems
import Silean.Modules.Mask.Mask
import Silean.Modules.BitwiseOr.BitwiseOr
import Silean.Modules.BinaryToOneHot.BinaryToOneHotTheorems
import Silean.Modules.CombMuxTree.CombMuxTreeTheorems
import Silean.Modules.RegisterBank.RegisterBankTheorems
import Silean.Modules.Mux.MuxTheorems
import Silean.Modules.EnabledRegister.EnabledRegisterDerived
import Silean.Modules.TupleField.TupleFieldTheorems
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterTheorems
import Silean.Modules.Equality.EqualityTheorems
import Silean.Modules.VectorConcat.VectorConcatTheorems
import Silean.Modules.VectorSplit.VectorSplitTheorems
import Silean.Modules.VectorSlice.VectorSliceTheorems
import Silean.Modules.VectorLayout.VectorLayoutTheorems
import Silean.Modules.EqualsConstant.EqualsConstantTheorems
import Silean.Modules.OneEntryFifo.OneEntryFifoCycleTheorems
import Silean.Modules.OneEntryFifo.OneEntryFifoFifoTheorems
import Silean.Modules.SerialDepthFifo.SerialDepthFifoCycleTheorems
import Silean.Modules.SerialDepthFifo.SerialDepthFifoFifoTheorems

/-! # Reusable hardware modules

This aggregate exports concrete reusable components built from primitives and
other certified modules. A main module file owns its boundary, behavior, and
cycle contract, plus a readable authored construction when one exists.
Expanded, recursive, or highly dependent structure belongs under `Internal/`.
The public derived or theorem facade exposes placement and correctness without
exposing structural proof machinery.

Generic construction patterns parameterized by an operation or family of
children belong under `Composition`; application-scale demonstrations belong
under `Examples`.
-/
