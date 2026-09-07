# Examples and checks

This directory contains code that exercises Silean rather than reusable
library components. Everything here is compiled, so declarations written as
Lean `example`s are checked by the same build as the library.

## Checks

`Checks/` contains focused compile-time tests and regression scenarios. These
files use concrete values to verify definitions, contracts, generated
authoring declarations, emitted FIRRTL, and previously problematic edge cases.
Reusable definitions and public theorems belong with the library code instead;
checks belong here when their primary purpose is to make the build reject an
incorrect change.

## Fixtures

`Fixtures/` contains definitions shared by multiple checks. Some fixtures are
small hardware hierarchies, such as `Not` and `DualNot`. Others are test-data
builders: `PicoRVControl` and `PicoRVDatapath` provide neutral inputs and
convenient state constructors for the focused PicoRV checks. They do not
replace or redefine the corresponding PicoRV contracts.

## PicoRV

`PicoRV/` is a substantial example port of a selected PicoRV32 configuration.
Unlike the small regression checks, it explores how Silean scales to a
realistic hierarchy and preserves source-level hardware behavior. Its local
[`README.md`](PicoRV/README.md) records the configuration, ownership decisions,
and current verification status.
