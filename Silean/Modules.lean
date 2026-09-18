import Silean.Modules.BitMux.BitMuxTheorems
import Silean.Modules.Constant.Constant
import Silean.Modules.All.All
import Silean.Modules.Any.Any
import Silean.Modules.HalfAdder.HalfAdderTheorems
import Silean.Modules.FullAdder.FullAdderTheorems
import Silean.Modules.Add.AddTheorems
import Silean.Modules.BitwiseXor.BitwiseXor
import Silean.Modules.BitwiseAnd.BitwiseAnd
import Silean.Modules.AddSub.AddSubTheorems
import Silean.Modules.Increment.IncrementTheorems
import Silean.Modules.Register.RegisterTheorems
import Silean.Modules.ResetRegister.ResetRegisterTheorems
import Silean.Modules.EnabledResetRegister.EnabledResetRegisterTheorems
import Silean.Modules.EnabledResetCounter.EnabledResetCounterTheorems
import Silean.Modules.Fifo.FifoFifoTheorems
import Silean.Modules.Mask.Mask
import Silean.Modules.BitwiseOr.BitwiseOr
import Silean.Modules.BinaryToOneHot.BinaryToOneHotTheorems
import Silean.Modules.CombMuxTree.CombMuxTreeTheorems
import Silean.Modules.RegisterBank.RegisterBankTheorems
import Silean.Modules.Mux.MuxTheorems
import Silean.Modules.EnabledRegister.EnabledRegisterTheorems
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
other certified modules. Fixed composites generally keep their readable
design and cycle contract in the main module file, public guarantees in a
`*Theorems.lean` file, and structural proof machinery under `Internal/`.
Recursive or highly dependent generators may use ordinary Lean internally,
but expose the same public structure, contract, certification, and naming
concepts wherever applicable.

Generic construction patterns parameterized by an operation or family of
children belong under `Composition`; application-scale demonstrations belong
under `Examples`.
-/
