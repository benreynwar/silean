import PicoRV.ControlContract
import PicoRV.Internal.ControlStructure

/-! # PicoRV control module

This is the public definition entry point for the complete registered control
hierarchy. `ControlContract.lean` states its source-level cycle behavior;
`Internal/ControlStructure.lean` contains the exhaustive typed architectural
connection map used by verification and emission.

The integration shell deliberately keeps that explicit map as its primary
structural representation. Its content is the named connection table between
the state register, `ControlNext`, and boundary outputs; a builder description
would repeat the same table rather than clarify it. -/
