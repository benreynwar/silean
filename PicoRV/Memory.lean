import PicoRV.MemoryContract
import PicoRV.Internal.MemoryStructure

/-! # PicoRV memory-interface module

This is the public definition entry point for the complete registered memory
interface. `MemoryContract.lean` states its source-level cycle behavior;
`Internal/MemoryStructure.lean` contains the exhaustive typed architectural
connection map used by verification and emission.

The integration shell keeps that explicit map as its primary structural
representation because its useful content is the named interconnection of
storage, look-ahead, formatting, response, and next-state children. -/
