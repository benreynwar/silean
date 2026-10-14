import Silean.Naming.ModuleNaming
import Silean.Naming.PrimitiveNaming
import Silean.Naming.SignalAdapterNaming
import Silean.Naming.FifoPortsNaming
import Silean.Naming.ReductionNaming
import Silean.Naming.FifoSerialNaming

/-! # Emission naming

This aggregate exports the metadata that maps typed structural labels and
hierarchy onto stable source and FIRRTL names. Naming is kept separate from
`ModuleStructure`: it affects rendered identities and aggregate component
names, but not connectivity, structural equations, contracts, or proofs.
-/
