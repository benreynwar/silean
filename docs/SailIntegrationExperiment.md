# Sail integration feasibility experiment

This experiment checked whether the locally cloned `sail-riscv32-lean` model
can serve as the independent architectural reference for PicoRV32. It did not
add Sail as a Silean dependency or commit to a particular proof invariant.

## Result

The generated model is usable as a semantic reference, but not yet as a direct
Silean dependency.

The model builds successfully with its pinned Lean 4.29 toolchain and
`lean-sail` revision. After that build, a separate file importing
`LeanRV32D.Step` typechecked in about one second and could refer directly to:

- `run_hart_active`, which performs a complete architectural hart step;
- `execute_ITYPE`, used for ordinary immediate arithmetic;
- `execute_LOAD` and `execute_STORE`; and
- the generated sequential state's byte-addressed memory.

The clean connection point is therefore real: a narrow adapter can select the
RV32I configuration and present Sail execution through a small interface owned
by Silean.

## Important limitations

The initial build is much too expensive for Silean's normal feedback loop. The
full generated model has 135 build targets; in this experiment `Defs` took
57 seconds, `PlatformConfig` took 86 seconds, and `InstsEnd` took 219 seconds.
Silean currently uses Lean 4.32.1 while the Sail repository pins Lean 4.29.0.
Version alignment must be tested separately before the repositories can share
one Lake build.

More importantly, the generated `SailM` is a concrete `EStateM` over registers
and a byte-addressed memory. Its low-level `sail_mem_read` and
`sail_mem_write` operations update that state directly. Although the generated
model calls `mem_read_callback` and `mem_write_callback`, both callbacks return
`Unit` and discard their arguments. Consequently the current model does not
directly expose the ordered load/store trace needed by our public observation.

## Recommended boundary

Do not import the full generated model throughout Silean. Put it behind one
adapter package or library. The public CPU property should compare completed
external observations, while stronger instruction or memory-transaction
correspondence remains private proof machinery.

The adapter needs to expose an RV32I execution relation together with its
ordered architectural memory operations. There are two plausible ways to get
that trace:

1. make a small upstreamable change to `lean-sail` so its memory semantics can
   record operations, then regenerate or rebuild the model; or
2. define a small RV32I-facing semantics in Silean and prove that it agrees
   with the relevant generated Sail instruction functions.

The first option preserves Sail as the direct executable relation but requires
maintaining a small backend extension. The second keeps Silean fast and clean,
but moves the Sail connection into a separate bridge proof. Before choosing,
the next experiment should instrument one load and one store and determine how
large the required `lean-sail` change actually is.

No relation between the complete Sail architectural state and a physical
PicoRV32 cycle state is part of the public specification. Such a relation may
still be useful privately when proving that a finite group of hardware cycles
implements one Sail instruction.
