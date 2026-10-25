# Running sum

Running sum reads signed decimal integers from stdin and writes the cumulative total after each
line.  Decimal magnitude is limited by guest memory and container-size bounds.  Executable
digits, lengths, indices, counts, and statuses use `UInt64`.

## Input and output

A line contains an optional `+` or `-`, at least one ASCII digit, and an optional trailing CR.
LF ends a line.  EOF also ends a nonempty final line.  Leading zeros and signed zero print in
canonical form.  Blank lines, spaces, and other bytes cause exit status 28.  The program preserves
output from preceding valid lines and stops before processing another line.

The program reads chunks of at most 4,096 bytes.  It retains a partial line across reads and
finishes pending output before processing the next line.  A short successful write retains the
unwritten suffix.  A successful zero-byte write retries that suffix.  A returned I/O error stops
with its errno.  Host traps preserve the effects committed before the trap.

For input `12`, `-5`, and `20` on separate lines, output is `12`, `7`, and `27` on separate lines.
Each completed line produces output before the next blocking read.

## Implementation and proofs

| Module | Contents |
|---|---|
| [Decimal arithmetic](Program.lean) | Parsing, magnitude comparison, signed addition, and decimal rendering. |
| [Arithmetic compilation](Compiled.lean) | Verified compilation of the six pure arithmetic functions. |
| [Stream process](Stream.lean) | Buffered input, pending output, error handling, and the EOF process. |
| [Action compilation](Wasi.lean) | Reflection and source-correspondence proofs for the bounded effectful steps. |
| [Command module](Module.lean) | The unbounded Wasm loop, stack admission check, binary encoding, and validity proofs. |
| [Application execution proof](Proof.lean) | Initial-store invariants, native-process correspondence, `_start` refinement, and the byte theorem. |
| [Native executable](Native.lean) | The same process with a [POSIX fd 0 reader](read.c) and flushed Lean output streams. |

`implements` classifies every modeled run that completes without exhausting Talos fuel.  A
normally stopped native process returns a status, which the compiled command passes to
`proc_exit`.  The theorem preserves the ordered effects and final world of those steps and the
accepted or rejected exit request.  A permitted guest resource trap matches a native process
prefix and residual action.  `run_initial` establishes this result from the modeled initial
store.  `bytes` combines the execution statement with encoding, exact decoding, and binary
validity.

These theorems require a host satisfying the WASI specification, the allocator invariant, valid
static bytes, and a memory cap of at most 65,535 pages.  The loop releases the old owned state
after each completed step.  [The WASI manual](../../docs/wasi.md) states the host, engine, and
file-emission assumptions.  Termination requires progress and resource premises.  The generic
[ranked loop rules](../../Verified/Wasi/ProcessTermination.lean) require bounded iteration proofs
and a decreasing natural-valued rank.  Running sum's execution theorem proves partial correctness.

The arithmetic tests compare results with Lean `Int`, including long carry, borrow, and
cancellation.  A general mathematical proof relating the digit-array arithmetic to `Int` remains
open.

The native reader returns after one successful `read` call and retries interrupted calls.  OS
errors propagate through Lean's `IO.Error` API.  This gives the executable short reads on pipes.
The generic `Process.runStdio` interpreter uses Lean's stream reader, whose pinned implementation
can wait for the requested capacity or EOF.  The native adapter and OS behavior require external
execution tests.

## Build and run

Commands run from the repository root.  The [host setup](../../docs/leanexe-manual.md#the-wasmtime-host)
provides the pinned Wasmtime host.

```sh
tests/running-sum/run.sh
printf '12\n-5\n20\n' | .lake/build/bin/running-sum-native
printf '12\n-5\n20\n' | build/tools/leanexe-wasmtime-host run build/running-sum/sum.wasm
```

[The application driver](../../tests/running-sum/run.sh) builds the proofs, audits their axioms,
tests native arithmetic and stream handling, exercises scripted Wasm transfers and failures,
compares native and Wasmtime output and status, and checks interactive output before EOF.
