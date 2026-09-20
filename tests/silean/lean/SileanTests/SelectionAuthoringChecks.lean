import Silean.Modules.Mux.Mux
import Silean.Modules.BitMux.BitMux
import Silean.Modules.VectorConcat.VectorConcat
import Silean.Modules.VectorSplit.VectorSplit
import Silean.Modules.VectorLayout.VectorLayout
import Silean.Modules.VectorSlice.VectorSlice
import Silean.Modules.TupleField.TupleField
import Silean.Modules.NamedTupleAdapter.NamedTupleAdapter

assert_not_imported Silean.Modules.Mux.Internal.MuxStructure
assert_not_imported Silean.Modules.BitMux.Internal.BitMuxStructure
assert_not_imported Silean.Modules.VectorConcat.Internal.VectorConcatStructure
assert_not_imported Silean.Modules.VectorSplit.Internal.VectorSplitStructure
assert_not_imported Silean.Modules.VectorLayout.Internal.VectorLayoutStructure
assert_not_imported Silean.Modules.VectorSlice.Internal.VectorSliceStructure
assert_not_imported Silean.Modules.TupleField.Internal.TupleFieldStructure
assert_not_imported Silean.Modules.NamedTupleAdapter.Internal.NamedTupleAdapterStructure

namespace SileanTests.SelectionAuthoring

#check Silean.Modules.Mux.cycleContract
#check Silean.Modules.BitMux.cycleContract
#check Silean.Modules.VectorConcat.cycleContract
#check Silean.Modules.VectorSplit.cycleContract
#check Silean.Modules.VectorLayout.cycleContract
#check Silean.Modules.VectorSlice.cycleContract
#check Silean.Modules.TupleField.cycleContract
#check Silean.Modules.NamedTupleCombiner.cycleContract
#check Silean.Modules.NamedTupleSplitter.cycleContract

end SileanTests.SelectionAuthoring
