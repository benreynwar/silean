import PicoRV.DecoderContract
import PicoRV.Internal.DecoderStructure

/-! # PicoRV decoder module

This is the public definition entry point for the complete two-stage decoder.
`DecoderContract.lean` states its source-level cycle behavior;
`Internal/DecoderStructure.lean` contains the exhaustive typed connection map
between capture and resolve stages.

The integration shell keeps that explicit map as its primary structural
representation because the named stage-to-stage and boundary connections are
the architectural content a reader needs to audit. -/
