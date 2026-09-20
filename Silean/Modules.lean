import Silean.Modules.BitMux.BitMuxDerived
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
import Silean.Modules.Fifo.FifoDerived
import Silean.Modules.Mask.Mask
import Silean.Modules.BitwiseOr.BitwiseOr
import Silean.Modules.BinaryToOneHot.BinaryToOneHotDerived
import Silean.Modules.CombMuxTree.CombMuxTreeDerived
import Silean.Modules.RegisterBank.RegisterBankDerived
import Silean.Modules.Mux.MuxDerived
import Silean.Modules.EnabledRegister.EnabledRegisterDerived
import Silean.Modules.TupleField.TupleFieldDerived
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterDerived
import Silean.Modules.Equality.EqualityDerived
import Silean.Modules.VectorConcat.VectorConcatDerived
import Silean.Modules.VectorSplit.VectorSplitDerived
import Silean.Modules.VectorSlice.VectorSliceDerived
import Silean.Modules.VectorLayout.VectorLayoutDerived
import Silean.Modules.EqualsConstant.EqualsConstantDerived
import Silean.Modules.OneEntryFifo.OneEntryFifoDerived
import Silean.Modules.SerialDepthFifo.SerialDepthFifoDerived

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
