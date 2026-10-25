# Running sum

Running sum reads signed decimal integers from stdin and writes the cumulative total after each
line.  Decimal magnitude is limited by guest memory and container-size bounds.  Executable
digits, lengths, indices, counts, and statuses use `UInt64`.  The mathematical `Nat`/`Int`
values and termination ranks are proof-only.

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
| [Integer specification](Spec.lean) | Positional decimal value, normalization, and executable-length bounds. |
| [Parser correctness](Parsing.lean) | Optional sign and CR syntax, acceptance, integer value, and normalization. |
| [Addition correctness](Addition.lean) | Signed integer addition, including cancellation and negative zero. |
| [Renderer correctness](Rendering.lean) | Canonical signed decimal encoding from `Nat.digits`, followed by LF. |
| [Mathematical stream model](StreamModel.lean) and [input bounds](InputBounds.lean) | Cumulative sums under independent line and prefix-sum size bounds. |
| [Arithmetic compilation](Compiled.lean) | Verified compilation of the six pure arithmetic functions. |
| [Stream process](Stream.lean) | Buffered input, pending output, error handling, and the EOF process. |
| [Action compilation](Wasi.lean) | Reflection and source-correspondence proofs for the bounded effectful steps. |
| [Command module](Module.lean) | The unbounded Wasm loop, stack admission check, binary encoding, and validity proofs. |
| [Process refinement](Proof.lean) | Initial-store invariants, native-process correspondence, `_start` partial refinement, and the byte theorem. |
| [Stream-host assumptions](StreamHost.lean) and [observed output](StreamObserved.lean) | Input consumption, committed stdout prefixes, EOF, and zero-write progress. |
| [Integer process correctness](StreamCorrect.lean) | Native process termination and canonical cumulative integer output. |
| [Compiled termination](TerminationTarget.lean) | Well-founded process progress, typed allocation budgets, and accepted exit. |
| [Compiled integer correctness](Correct.lean) | Cumulative stdout and eventual accepted exit 0 from the modeled initial store, with an encoded-byte theorem. |
| [Native executable](Native.lean) | The same process with a [POSIX fd 0 reader](read.c) and flushed Lean output streams. |

`parse_correct`, `add_correct`, and `render_correct` relate the decimal arithmetic to `Int`.
`process_terminates_integer` connects the native process to the mathematical prefix sums.
`initial_terminates_integer` proves that the compiled command eventually exits with accepted
status 0 and writes exactly those sums in canonical signed decimal form, each followed by LF.
It supplies a fuel threshold valid for every larger Talos fuel value.  `integer_bytes` combines
that theorem with encoding, exact decoding, and binary validity.  Talos represents accepted
`proc_exit` by the designated exit trap and records status 0 in the final host world.

The theorem starts with an empty event journal and output history and uses these premises:

| Premise | Requirement |
|---|---|
| [Valid input](StreamModel.lean) | `StreamModel.ValidInput` decomposes the finite input into decimal lines, with LF boundaries and an optional nonempty final line at EOF. |
| [Integer sizes](InputBounds.lean) | `InputBounds` requires `line.size + 3 < 2^64` for each line and `integerDigitCount sum + 3 < 2^64` for every mathematical prefix sum.  These conditions bound lines and sums independently of the total input length. |
| [Host behavior](StreamHost.lean) | `StreamHost` supplies successful reads and writes, consumes input prefixes, reports empty input only at EOF, and commits output prefixes.  Every zero-byte write decreases a proof-only natural-valued credit.  The Talos host also satisfies the WASI specification. |
| [Allocation and depth](Correct.lean) | `RunResources` supplies `Heap.Within` and a typed `Resource.CallPrefixBound` at begin and every finite reached active step call.  `LocalsHold` ties the represented state to the iteration's local words. |
| [Final exit](Correct.lean) | `ExitAccepted` excludes rejection of status 0 or 28 at represented host worlds.  The valid-input theorem exits with status 0. |

A numeric whole-input memory bound remains unproved.

`implements` and `run_initial` remain partial refinement theorems.  They classify every modeled
run that completes without exhausting Talos fuel.  A normally stopped native process returns
a status, which the compiled command passes to `proc_exit`.  The theorem preserves the ordered
effects and final world of those steps and the accepted or rejected exit request.  A permitted
guest resource trap matches a native process
prefix and residual action.  `run_initial` establishes this result from the modeled initial
store.  `bytes` combines the execution statement with encoding, exact decoding, and binary
validity.

The compiled refinement requires a host satisfying the WASI specification, the allocator
invariant, valid static bytes, and a memory cap of at most 65,535 pages.  The loop releases the
old owned state after each completed step.  [The WASI manual](../../docs/wasi.md) states the host, engine, and
file-emission assumptions.  The generic
[total-process theorem](../../Verified/Wasi/ProcessTotalCorrect.lean) uses an application-supplied
well-founded progress relation, resource budgets at reached calls, and final-exit acceptance.

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
