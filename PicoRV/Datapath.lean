import PicoRV.DatapathContract
import PicoRV.Internal.DatapathStructure

/-! # PicoRV datapath module

This is the public definition entry point for the complete registered
datapath. `DatapathContract.lean` states its source-level cycle behavior;
`Internal/DatapathStructure.lean` contains the exhaustive typed architectural
connection map used by verification and emission.

The integration shell keeps that explicit map as its primary structural
representation because the named connections among storage, ALU, next-state
logic, and writeback selection are precisely what a reader needs to audit. -/
