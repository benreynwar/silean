# Silean tests and fixtures

The Silean-specific Lean checks and fixtures live under
`tests/silean/lean/SileanTests`. Everything there is compiled, so declarations
written as Lean `example`s are checked by the same build as the library.

## Checks

The test directory contains focused compile-time tests and regression scenarios. These
files use concrete values to verify definitions, contracts, generated
authoring declarations, emitted FIRRTL, and previously problematic edge cases.
Reusable definitions and public theorems belong with the library code instead;
checks belong here when their primary purpose is to make the build reject an
incorrect change.

## Fixtures

Its `Fixtures/` directory contains definitions shared by multiple checks. Some fixtures are
small hardware hierarchies, such as `Not` and `DualNot`. Others are test-data
PicoRV-specific fixtures instead live under
`tests/picorv/lean/PicoRVTests/Fixtures`.

## PicoRV

The top-level `PicoRV/` library is a substantial client of Silean rather than a
subdirectory of its test suite. Its [`README.md`](../picorv/README.md) records
the configuration, ownership decisions, and current verification status.
