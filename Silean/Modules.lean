import Silean.Modules.BitMux.BitMuxCertified
import Silean.Modules.Constant.Constant
import Silean.Modules.All.All
import Silean.Modules.Any.Any
import Silean.Modules.HalfAdder.HalfAdderCertified
import Silean.Modules.FullAdder.FullAdderCertified
import Silean.Modules.Add.Add
import Silean.Modules.BitwiseXor.BitwiseXor
import Silean.Modules.BitwiseAnd.BitwiseAnd
import Silean.Modules.AddSub.AddSubCertified
import Silean.Modules.Increment.Increment
import Silean.Modules.Register.Register
import Silean.Modules.ResetRegister.ResetRegisterCertified
import Silean.Modules.EnabledResetRegister.EnabledResetRegisterCertified
import Silean.Modules.EnabledResetCounter.EnabledResetCounterCertified
import Silean.Modules.Fifo.FifoCertified
import Silean.Modules.Mask.Mask
import Silean.Modules.BitwiseOr.BitwiseOr
import Silean.Modules.BinaryToOneHot.BinaryToOneHot
import Silean.Modules.CombMuxTree.CombMuxTree
import Silean.Modules.RegisterBank.RegisterBankCertified
import Silean.Modules.Mux.MuxCertified
import Silean.Modules.EnabledRegister.EnabledRegisterCertified
import Silean.Modules.TupleField.TupleFieldCertified
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapterCertified
import Silean.Modules.Equality.Equality
import Silean.Modules.VectorConcat.VectorConcatCertified
import Silean.Modules.VectorSplit.VectorSplitCertified
import Silean.Modules.VectorSlice.VectorSliceCertified
import Silean.Modules.VectorLayout.VectorLayoutCertified
import Silean.Modules.EqualsConstant.EqualsConstantCertified
import Silean.Modules.OneEntryFifo.OneEntryFifoFifoCertified
import Silean.Modules.SerialDepthFifo.SerialDepthFifoFifoCertified

/-! # Reusable hardware modules

This aggregate exports concrete reusable components built from primitives and
other certified modules. Fixed composites generally keep their readable
design and cycle contract in the main module file and their structural proof
in a sibling `*Certified.lean` file. Recursive or highly dependent generators
may use ordinary Lean internally, but expose the same public structure,
contract, certification, and naming concepts wherever applicable.

Generic construction patterns parameterized by an operation or family of
children belong under `Composition`; application-scale demonstrations belong
under `Examples`.
-/
