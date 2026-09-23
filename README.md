# Silean

WARNING:  On a scale of 0 to 10, where 0 is a project I wrote myself, and 10 is
a project entirely written by an LLM, this project is an 8.

My main role has been setting goals and keeping it going in vaguely the right
direction.  It's an experiment to see if a proof-assistant-embedded approach to
hardware design is practical yet. The "documentation" files are all LLM
generated at the moment and I wouldn't trust them too much.

About two years ago I had a go at writing an HDL embedded in dafny
([Silemma](https://github.com/benreynwar/silemma)).  I made some
progress, but it ended up being too difficult for me.  Now that LLMs have
gotten pretty good at writing proofs I decided it was time to have another go,
but this time using Lean4 and an LLM.

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
- the multiplier, butterfly, and generic unrolled FFT have certified Silean
  implementations; and
- the complete streaming hierarchy has natural top-down contracts, with the
  concrete rolled stage and packet reorderers still to be implemented.

The repository also contains certified FIFO examples and a structural PicoRV
client. The complete PicoRV source-equivalence and architectural-refinement
proofs remain future work.

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

The HTFFT mathematical, numerical, arithmetic, and unrolled-network results are
proved. Its full streaming hardware theorem remains conditional until the
rolled stages and packet reorderers are concretely implemented.

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
- [`HTFFT/Plan.md`](HTFFT/Plan.md) records the current FFT work.
- [`PicoRV/`](PicoRV/) and [`RV32I/`](RV32I/) contain the processor client
  and its clean architectural model.
- [`docs/silean/Architecture.md`](docs/silean/Architecture.md) describes the
  framework in detail.
- [`Roadmap.md`](Roadmap.md) records the project-wide direction.
