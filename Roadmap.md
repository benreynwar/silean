# Silean roadmap

This file contains planned future work only. Current capabilities and design
decisions are documented in the root [`README.md`](README.md), the
[architecture guide](docs/silean/Architecture.md), and the
[HTFFT overview](HTFFT/README.md).

## Validate the complete HTFFT RTL

Select a modest concrete transform size, samples-per-cycle count, fixed-point
format, and pipeline placement. For that configuration:

1. inspect the closed `ModuleStructure` hierarchy and arithmetic widths;
2. emit FIRRTL and lower it to SystemVerilog;
3. simulate deterministic complete frames;
4. check values, natural output ordering, `i_first`/`o_first` timing, exact
   latency, and back-to-back throughput; and
5. inspect shift-register construction and multiplier lowering.

## Audit proof trust

Review all production proofs for `sorry`, project axioms, `native_decide`, and
unsafe proof shortcuts. Record and enforce the distinction between
kernel-checked production proofs and evaluation mechanisms used only by tests
or executable examples.

## Reduce the backend trust boundary

Define the supported emitted subset precisely and either prove that rendering
preserves `ModuleStructure` semantics or introduce a smaller independently
checked translation boundary. FIRRTL generation, CIRCT lowering, and
SystemVerilog simulation currently provide regression evidence but are not
part of the formal correctness theorem.
