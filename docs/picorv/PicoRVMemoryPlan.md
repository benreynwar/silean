# PicoRV32 memory implementation and proof plan

## Purpose and scope

This document records the implementation and proof plan for the configured
PicoRV32 memory-interface block. The source of truth is
`../picorv32/picorv32.v` at commit
`a473fc8fca393771d83b0ffcf0b14db3393339d8`, specialized to the parameters in
[`PicoRV32Plan.md`](PicoRV32Plan.md). In particular,
`COMPRESSED_ISA = 0` and `LATCHED_MEM_RDATA = 0` remove the compressed-word
buffering paths and make returned data belong to the cycle in which
`mem_valid && mem_ready` is true.

The goal is a closed, stateful `PicoRVMemory` structure universally certified
against the existing contract in `Memory.lean`. This is a cycle-accurate
implementation of the core side of PicoRV32's memory protocol. It is not a
memory model and does not impose latency, address-map, or response assumptions
on the external environment.

Architectural correctness, reachable-state invariants, retirement traces,
Sail integration, and a general memory environment are deliberately outside
this plan.

This implementation milestone is complete: the standalone Memory hierarchy
and both remaining Decoder leaves are concrete, universally certified, and
recursively closed. They are substituted into the complete PicoRV hierarchy,
whose equations have a proved unique solution. Standalone and complete-core
closed FIRRTL emission, CIRCT lowering, Verilator lint, and representative
clocked regressions are build gates.

## Ownership and protocol model

Control owns the level commands `mem_do_prefetch`, `mem_do_rinst`,
`mem_do_rdata`, `mem_do_wdata`, and `mem_wordsize`. Datapath owns `next_pc`,
`reg_op1`, and `reg_op2`. The external environment owns `mem_ready` and
`mem_rdata`. Memory observes all of these and owns exactly seven registers:

- `mem_state`, the four-state request phase;
- `mem_valid`, `mem_instr`, `mem_addr`, `mem_wdata`, and `mem_wstrb`, which
  constitute the single registered external request; and
- `mem_rdata_q`, the most recently transferred response word.

The ordinary request outputs expose those registers directly. Therefore the
block can have at most one outstanding request, and backpressure retains the
entire request unchanged. The look-ahead outputs describe a request that can
start on the next edge; they do not constitute a second outstanding request.

The four `mem_state` encodings have the following natural meanings:

| Encoding | Contract phase | Meaning |
| ---: | --- | --- |
| `0` | `idle` | no request is being serviced |
| `1` | `readRequest` | instruction, prefetch, or data read is outstanding |
| `2` | `writeRequest` | data write is outstanding |
| `3` | `prefetched` | a pure prefetch response was captured before control requested the instruction |

Commands are intentionally level-sensitive. After `mem_done`, control must
deassert or change the completed command; otherwise returning to idle starts
another request. `Memory.CommandsWellFormed` captures the source assertions:
data reads and writes exclude all other commands, while prefetch and
instruction-read may overlap during promotion.

## Source-to-contract audit

The following table records the configured Verilog behavior and the matching
contract definition. The comparison is over arbitrary two-state inputs, not
only expected processor traces, except where a source `x` or `full_case`
requires an explicit totalization.

| Source behavior | Configured result | Contract status |
| --- | --- | --- |
| transfer | `mem_xfer = mem_valid && mem_ready` | matches `memXferFrom` |
| look-ahead read | reset released, idle, and any instruction/prefetch/data-read command | matches `memLaReadFrom` |
| look-ahead write | reset released, idle, and write command | matches `memLaWriteFrom` |
| look-ahead address | aligned `next_pc` for prefetch/instruction, otherwise aligned `reg_op1` | matches `memLaAddrFrom` |
| write formatting | word unchanged, halfword duplicated, or byte replicated four times | matches `formattedWriteDataFrom` |
| byte strobes | `1111`, selected halfword pair, or selected byte | matches `formattedWriteMaskFrom` |
| read formatting | word unchanged or selected zero-extended halfword/byte | matches `formattedReadDataFrom` |
| latched response view | live `mem_rdata` during transfer, otherwise `mem_rdata_q` | matches `memRdataLatchedFrom` |
| ordinary completion | reset released, transfer in a non-idle phase, and active instruction/read/write command | matches the first arm of `memDoneFrom` |
| delayed prefetch completion | state 3 and `mem_do_rinst`, with no new external transfer | matches the second arm of `memDoneFrom` |
| response capture | every external transfer writes `mem_rdata_q` | matches `responseCaptured` |
| idle request start | read-side command starts state 1; write command has later assignment priority and starts state 2 | matches state 0 in `normalNextState` |
| read completion | clear valid; return to idle for active instruction/data read, otherwise enter state 3 | matches state 1 in `normalNextState` |
| write completion | clear valid and return to idle | matches state 2 in `normalNextState` |
| prefetch promotion | `mem_do_rinst` returns state 3 to idle; `mem_done` is combinationally true that cycle | matches state 3 and `memDoneFrom` |
| reset/trap | reset forces state 0; reset or `mem_ready` clears valid; trap alone otherwise retains state and a stalled valid request | matches `nextState` |

### Timing and priority details

The Verilog has two clocked processes relevant to retained response and
request state. The response process captures `mem_rdata_q` on every transfer.
The request-state process separately handles reset/trap or the normal state
machine. Nonblocking assignments make both processes observe pre-edge values.
Consequently a response is still captured on an edge where reset or trap is
also asserted. The contract deliberately applies `responseCaptured` before
the reset/trap override to preserve that outcome.

In idle, the source uses two `if` statements rather than `if`/`else`: the
read-side assignment occurs first and the write assignment occurs second.
Thus a malformed simultaneous read and write command ends in write state with
write request flags. Look-ahead address selection still gives instruction-side
commands priority, because it is a separate combinational expression. The
contract preserves this behavior for universal certification even though
Control is expected to prove such a command combination unreachable.

A pure prefetch transfer is not reported complete to Control. It captures the
response, clears the external request, and enters state 3. A later
`mem_do_rinst` asserts `mem_done` without `mem_xfer`, allowing the already
captured word to be consumed. This distinction must appear in both checked
examples and a generated clocked test.

`mem_rdata_word` formats the live external `mem_rdata`, while
`mem_rdata_latched` selects live data exactly during transfer and otherwise
uses `mem_rdata_q`. These are intentionally different views. The top-level
timing arranges for Datapath to capture formatted data on completion.

### Configuration omissions and totalizations

With compressed instructions disabled, `mem_la_firstword`, second-word
requests, the 16-bit buffer, prefetched high-word tracking, response shuffling,
and the compressed contribution to `mem_xfer` are constant or dead. They must
not appear as latent state in the Silean implementation.

With `LATCHED_MEM_RDATA = 0`, the source's no-shuffle response expression uses
external `mem_rdata` only on transfer and otherwise uses `mem_rdata_q`. The
contract follows this configured behavior rather than supporting both
parameter settings.

The source's formatting block is marked `full_case` and has no assignment for
`mem_wordsize = 3`. The two-state contract totalizes that encoding as a word
access: raw write/read data and mask `1111`. `InputsWellFormed` records the
live source encodings `0`, `1`, and `2`; universal structural certification
will nevertheless prove the documented totalization for encoding `3`.

The source-local `mem_busy` is merely the OR of the four commands and has no
consumer in this configuration. It is therefore omitted from the boundary and
hardware structure. The natural `memBusy` helper may remain as a readable
view, but it imposes no additional hardware requirement.

## Proposed hierarchy

The stateful wrapper should make storage and current-cycle output timing
obvious:

```text
PicoRVMemory
|- inputsValue    : named input tuple combiner
|- storage        : aggregate Register MemoryState
|- stateFields    : named state tuple splitter
|- lookahead      : MemoryLookahead
|- readFormatting : MemoryReadFormatting
|- response       : MemoryResponse
|- next           : MemoryNext
`- output wiring
```

One aggregate register is appropriate because the source updates these seven
registers as one protocol state and the contract computes one complete next
state. It must be an ordinary register, not a uniformly reset register:
`mem_rdata_q`, request address/data/strobes, and `mem_instr` are deliberately
not reset by the source.

The combinational children have semantic boundaries:

- `MemoryLookahead` computes `mem_la_read`, `mem_la_write`, aligned address,
  formatted write data, and write strobes. Its internal structure may use
  separate address, data, and mask helpers so the source's address priority and
  the three formatting modes have local proofs.
- `MemoryReadFormatting` computes `mem_rdata_word` from the live response,
  word size, and address low bits.
- `MemoryResponse` computes `mem_done` and `mem_rdata_latched` from current
  state, commands, readiness, reset, and response data.
- `MemoryNext` computes the complete next aggregate state. It is the difficult
  part and should expose the state-machine structure rather than hiding the
  transition in an opaque primitive.

The proposed `MemoryNext` hierarchy follows assignment order:

```text
MemoryNext
|- responseCapture : conditionally replace mem_rdata_q
|- lookaheadCapture: conditionally replace request address/strobes/data
|- phaseDecode     : equality for phases 0, 1, 2, and 3
|- idleUpdate      : read start followed by write-priority start
|- readUpdate      : transfer to idle or prefetched
|- writeUpdate     : transfer to idle
|- prefetchedUpdate: instruction promotion to idle
|- phase selection
`- resetTrapOverride
```

Not every line above must become a separate emitted module. A child is useful
when it gives a meaningful source region and an independently stated theorem;
simple gates and field selection should use existing generic primitives.
Aggregate state-update adapters already used by Control and Datapath should be
reused instead of inventing a memory-specific wiring language.

## Natural correctness argument

The intended certification proof proceeds from the leaves to the stateful
wrapper.

### 1. Prove the pure data transformations

For arbitrary bit vectors, certify that alignment clears address bits 0 and
1, write formatting implements all four totalized word-size encodings, write
strobes select the correct lanes, and read formatting selects and
zero-extends the correct lane. These theorems must not assume aligned
`reg_op1`; its low bits are precisely what choose a byte or halfword lane.

### 2. Prove current-cycle combinational outputs

Certify `MemoryLookahead`, `MemoryReadFormatting`, and `MemoryResponse` against
their natural functions. In particular:

- look-ahead signals are suppressed during reset and outside idle;
- a stalled registered request does not produce another look-ahead request;
- `mem_done` requires a real transfer except for state-3 promotion; and
- the latched-data view selects the live bus on transfer and stored data
  otherwise.

No proof should assume well-formed commands or a reachable state. Source
priority resolves overlaps, and the circuit must agree with the total contract
for every input and current state.

### 3. Prove each next-state layer

Show, in source assignment order, that:

1. response capture equals `responseCaptured`;
2. look-ahead capture changes only the request fields assigned by the source;
3. each phase update equals its corresponding branch of `normalNextState`;
4. write start has later priority than read start in idle;
5. phase selection equals `normalNextState`; and
6. the final reset/trap layer equals `nextState`, including response capture on
   a simultaneous transfer and reset/trap edge.

These local equalities should culminate in a universal theorem of the form

```text
next.state = Memory.nextState inputs current
```

for arbitrary inputs, current state, and child proposals satisfying the
`MemoryNext` structural equations.

### 4. Relate aggregate storage to contract state

Use the explicit state correspondence

```text
storage state .stored = stateMap.pack memory contract state
```

and prove state coverage by unpacking an arbitrary aggregate value. The tuple
splitter then establishes that registered request outputs and `mem_rdata_q`
are the pre-edge contract state. The certified combinational children prove
the remaining output rules, and the `MemoryNext` theorem plus the generic
register state rule proves the edge transition.

### 5. Prove closure and uniqueness

Bundle the child certifications into a certification of the outer Memory
structure. Prove recursively that both `MemoryNext` and the complete
`PicoRVMemory` hierarchy contain no blackboxes. The existing cycle-contract
machinery then provides a unique evaluated output/next-state result for every
input and current state; no protocol premise is needed for uniqueness.

## Verification plan

Focused Lean examples should teach the protocol as short traces, not merely
exercise isolated helper functions. They must cover:

- an instruction look-ahead, registered request start, stall with stable
  request fields, transfer, response capture, completion, and return to idle;
- a data read with delayed readiness and correct word, low/high halfword, and
  all four byte selections;
- word, low/high halfword, and all four byte writes, including replicated data,
  aligned request address, and strobes;
- a pure prefetch transfer that enters state 3 without `mem_done`, followed by
  instruction promotion and completion without a second transfer;
- reset from idle and from a stalled request, showing pre-edge outputs versus
  post-edge state;
- transfer coincident with reset and with trap, demonstrating the exact source
  capture/clear/retain priorities;
- the malformed read/write overlap, documenting universal source priority;
- `mem_wordsize = 3`, documenting the chosen two-state totalization; and
- the universal certification, state coverage, unique-solution witness, and
  recursive no-blackbox theorem.

Generated hardware verification should include:

1. closed FIRRTL rendering of standalone `PicoRVMemory`;
2. CIRCT lowering to SystemVerilog;
3. Verilator lint of the generated hierarchy; and
4. a clocked regression that exercises reset, a stalled instruction fetch, a
   data read, representative byte/halfword/word writes, delayed prefetch
   completion, and reset during an outstanding request.

After Memory is substituted at the PicoRV top level, the same closed-render,
CIRCT, lint, and representative clocked checks must run for the complete core.
The top-level test supplies only a small deterministic memory responder; it is
not the general memory-environment model excluded from this goal.

## Implementation order

1. Add the focused missing contract examples, especially reset/trap transfer
   priority, malformed overlap, and word-size totalization.
2. Implement and certify `MemoryNext` first, beginning with response capture
   and the four phase updates. This is the highest-risk stateful logic.
3. Implement and certify alignment, formatting, look-ahead, and response
   children.
4. Assemble the aggregate-register wrapper and universally certify it against
   `Memory.cycleContract`.
5. Prove recursive no-blackbox closure and standalone unique evaluation.
6. Add the standalone emitter and generated clocked regression.
7. Implement and certify Decoder's instruction-match and instruction-summary
   children, retaining source match and illegal-instruction priority.
8. Substitute Memory and both Decoder children into the top-level hierarchy;
   recheck the full schedule, uniqueness proof, and zero-blackbox inventory.
9. Run the full Lean build and all closed FIRRTL, CIRCT, Verilator, and clocked
   generated-hardware gates.

## Completion criteria

The work is complete only when all of the following are checked:

- this audit still agrees with the configured source and every intentional
  two-state totalization is documented;
- focused examples cover all protocol and priority cases listed above;
- `PicoRVMemory` is universally certified against the existing contract;
- its complete standalone hierarchy contains no blackboxes and has a unique
  cycle solution;
- instruction-match and instruction-summary are concrete, universally
  certified, and recursively closed;
- all three former behavioral leaves are substituted at top level;
- the complete PicoRV hierarchy contains no blackboxes and its simultaneous
  equations have at most one solution;
- standalone Memory and complete-core FIRRTL render and lower through CIRCT;
- generated SystemVerilog passes Verilator lint and the specified clocked
  regressions; and
- the full Lean and repository test gates pass.
