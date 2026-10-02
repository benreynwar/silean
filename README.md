# Silean

```
WARNING: LLM Usage Scale
 0 - A project I wrote myself
 2
 4
 6
 8 <--------- THIS PROJECT
10 - A project entirely written by an LLM
```

This project is an experiment to see if a proof-assistant-centric approach to
hardware RTL design is practical yet.  The conclusion is that it is practical.
I've ported a high throughput FFT design that I wrote in VHDL 5 years ago
[github.com/benreynwar/htfft](github.com/benreynwar/htfft) to a version embedded
in lean and proved it's equivalence within a specified error bound to the 
Mathlib complex DFT.

This repository is a proof-of-concept work and is almost entirely LLM generated.
It is not a suitable base to build upon, but it is a reasonable demonstration
of the approach.  My main role has been setting goals and keeping the agent
going in vaguely the right direction.

At this point the project has served it's purpose and I'm no longer working on
it.  I'm currently working on a second version of this project that will be much
lower on the LLM Usage Scale.

The rest of this README is LLM generated.

## What we have found

The main result so far is encouraging: it is now quite practical to develop
structural hardware in Lean and prove useful properties about it, provided an
LLM does much of the proof engineering.

The resulting code still looks like hierarchical hardware—ports, instances,
wiring, registers, and reusable modules—but its specifications can be ordinary
Lean mathematics. The most useful design principle has been to keep those two
views separate:

- `ModuleStructure` describes concrete executable hardware as simultaneous
  structural equations.
- Independent contracts describe behavior naturally, without copying the
  implementation's wires or state.
- Refinement proofs connect the structure to its contract using public facts
  about child modules.

Lean checks the final proof terms; the LLM makes constructing and maintaining
them practical. The difficult part has increasingly been choosing good
abstractions and contracts rather than writing individual proof steps.

## Current state

Silean has a typed structural hardware model, an authoring DSL, compositional
certification machinery, reusable arithmetic and storage modules, and direct
FIRRTL generation.

The main active client is `HTFFT`, a Lean/Silean port of the fixed-point
streaming FFT at [benreynwar/htfft](https://github.com/benreynwar/htfft):

- the exact radix-2 FFT is proved equal to Mathlib's complex DFT;
- the fixed-point model has explicit no-overflow conditions and a proved
  numerical error bound;
- its arithmetic, unrolled prefix, rolled stages, and packet reorderers have
  certified Silean implementations; and
- the closed streaming hierarchy has an end-to-end hardware-to-DFT accuracy
  theorem.

The repository also contains certified FIFO examples that exercise the
framework independently of the FFT client.

Top-down designs use `ModuleBody`: it records ports, child interfaces, and
wiring without pretending that unresolved children have executable blackbox
semantics. Parent contracts can be proved conditionally from explicit
properties of synchronized child traces, then reused when concrete children
are supplied.

## What is and is not proved

WARNING: Just a quick reminder that the content here (but not these two sentences)
was written by an LLM.  I'm not yet confident myself about exactly what is and
isn't proven.

For certified modules, Lean proves that the concrete structural equations have
the required behavior. Existence and uniqueness results prevent correctness
from being vacuously derived from inconsistent equations.

The formal boundary currently ends at `ModuleStructure`. Generated FIRRTL and
SystemVerilog are compiled and simulated, but the renderer is not yet proved
semantics-preserving. Signal semantics are two-state Boolean semantics and do
not model timing, metastability, `X`, or `Z`.

The HTFFT mathematical, numerical, and complete streaming-hardware results are
proved. Generated RTL is still validation evidence rather than part of the
formal theorem.

## Trying it

The recommended environment is the checked-in Nix flake:

```sh
nix develop
lake build Silean SileanTests
lake build HTFFT HTFFTTests
```

Generated-hardware regressions use CIRCT, Verilator, and cocotb:

```sh
make test
```

## Where to look

- [`Silean/`](Silean/) contains the reusable framework and module library.
- [`HTFFT/`](HTFFT/) contains the FFT specifications, proofs, and hardware.
- [`HTFFT/README.md`](HTFFT/README.md) explains the FFT architecture, proof,
  and remaining validation work.
- [`docs/silean/Architecture.md`](docs/silean/Architecture.md) describes the
  framework in detail.
- [`Roadmap.md`](Roadmap.md) records the project-wide direction.
