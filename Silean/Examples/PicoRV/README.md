# PicoRV32 port

This directory owns the PicoRV32-specific interfaces, behavioral
specifications, and eventually the direct hardware port. It is an example
design rather than general-purpose Silean library machinery.

The first milestone is contract-only. Before adding any PicoRV32 child
implementation, define and review the exact configured ports and the
appropriate behavioral specification for every direct child:

- `PicoRV32Control`;
- `PicoRV32Memory`;
- `PicoRV32Decoder`;
- `PicoRV32Regs`;
- `PicoRV32Alu`; and
- `PicoRV32Rvfi`.

Contract form follows the natural abstraction. In particular, the memory and
RVFI specifications are temporal properties; they must not be forced into a
`ModuleCycleContract` merely because that contract form already exists.

Keep source names from `picorv32.v` in structural port maps. Lean-facing
interpretations may introduce clearer datatypes and projections without
renaming those hardware signals. General modules discovered while doing the
port belong in `Silean/Modules/`, not here.
