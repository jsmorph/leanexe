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
the Wasm module with its errno as the exit status.  The native executable raises the error as a
Lean `IO.Error`, prints it, and exits with status 1.  Host traps preserve the effects committed
before the trap.

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
| [Line kernel](Kernel.lean) | Line kernel and its specification for [the shared stream proofs](../StreamFold/README.md): normal totals, size room, and nonempty output. |
| [Line model and size bounds](Model.lean) | `InputBounds`, the line rooms that it implies, and the outputs and status of the kernel's fold over the input lines. |
| [Arithmetic compilation](Compiled.lean) | Verified compilation of the six pure arithmetic functions. |
| [Stream process](Stream.lean) | Buffered input, pending output, error handling, and the EOF process. |
| [Stream view](StreamView.lean) and [termination](Termination.lean) | Relation between the process and the shared stream process, and the progress of each step. |
| [Action compilation](Wasi.lean) | Reflection and source-correspondence proofs for the bounded effectful steps. |
| [Command module](Module.lean) | Unbounded Wasm loop, stack admission check, binary encoding, and validity proofs. |
| [Process refinement](Proof.lean) | Initial-store invariants, native-process correspondence, `_start` partial refinement, and the byte theorem. |
| [Integer process correctness](StreamCorrect.lean) | `InputValues`, native process termination, and the canonical cumulative output of the lines before the first rejected line. |
| [Compiled termination](TerminationTarget.lean) | Well-founded process progress, an invariant of the reached states, typed allocation charges, and accepted exit. |
| [Limits and invariant](Limits.lean) | `InputLimits L D`, the kernel specification `limitSpec L D`, the invariant `LimitInv L D` of the reached states, and the sizes of every state that a step returns. |
| [Charges](Charges.lean) | Allocation charges of `begin` and of each step, from the generated bounds of the pure functions, the bound of 4,320 bytes on the charge of `begin`, and the bound `stepCharge L D` on the charge of a step from a state within the limits. |
| [Compiled integer correctness](Correct.lean) | Cumulative stdout and eventual accepted exit with status 0 or 28 from the modeled initial store, with an encoded-byte theorem. |
| [Native executable](Native.lean) | Same process with a [POSIX fd 0 reader](read.c) and flushed Lean output streams. |

`parse_correct`, `add_correct`, and `render_correct` relate the decimal arithmetic to `Int`.
`InputValues input values status` holds when `values` are the integers of the input lines before
the first line that is not a decimal integer, with `status` 0 when every line is one and 28
otherwise.  `inputValues_exist` and `inputValues_unique` show that every input within the size
bounds determines one such pair.  `process_terminates_integer` connects the native process to
the cumulative sums of `values`.  `initial_terminates_integer` proves, for all limits `L` and `D`
with `4104 + limitMemory L D ≤ 65536 · 65535` and every input within the size bounds and those
limits, that the compiled command eventually exits with accepted status `status` and writes
exactly those sums in canonical signed decimal form, each followed by LF.  It supplies a fuel
threshold valid for every larger Talos fuel value.  `initial_terminates_integer_9000000` fixes
both limits at 9,000,000, for which that inequality holds.  `integer_bytes` combines the general
theorem with encoding, exact decoding, and
binary validity.  Talos represents accepted `proc_exit` by the
designated exit trap and records the status in the final host world.

The theorem starts with an empty event journal and output history and uses these premises:

| Premise | Requirement |
|---|---|
| [Integer sizes](Model.lean) | `InputBounds` requires `line.size + 3 < 2^64` for each line of the input and `integerDigitCount total + 3 < 2^64` for the total of each prefix of valid lines.  These conditions give the kernel's size condition `Room`, `max total.digits.size line.size + 3 < 2^64`, at each line. |
| [Limits](Limits.lean) | `InputLimits L D` requires at most `L` bytes in each line up to and including the first line that is not a decimal integer, and at most `D` digits in the total after each line before it. |
| [Memory](Correct.lean) | The literal pool ends 4,104 bytes into memory, and that end plus `limitMemory L D = 220 · (L + D) + 1,010,000` bytes must lie within the memory cap of 65,535 pages. |
| [Host behavior](../StreamFold/StreamHost.lean) | `StreamHost` supplies successful reads and writes, consumes input prefixes, reports empty input only at EOF, and commits output prefixes.  Each zero-byte write decreases a proof-only natural-valued credit, and a read or a write of at least one byte may set the credit to any value.  The Talos host also satisfies the WASI specification. |
| [Final exit](Correct.lean) | `ExitAccepted` excludes rejection of status 0 or 28 at represented host worlds. |

The process compacts its state after `begin` and after each step: it copies the state above the
heap's top and moves the copy down to the heap's base, the heap top when `_start` began, so
between steps the heap holds the literal pool and one state.  The memory a run needs therefore does
not grow with the number of lines or the total length of the input.  Each step needs room for the
copy of the state before it, its allocation, and the copy of the state after it.  Within the
limits, a copy of a state costs at most `9 · D + 8 · L + 4,320` bytes, and a step at most
`200 · (L + D) + 1,000,500` bytes: a step that consumes input pushes at most 4,096 bytes onto the
pending line at 80 bytes each and completes at most one line.  `limitMemory L D` covers both
copies and the step, as `limitMemory_room` proves:
`2 · (9 · D + 8 · L + 4,320) + 200 · (L + D) + 1,000,500 ≤ 220 · (L + D) + 1,010,000`.  These
bounds concern native states and stream positions, and the invariant `LimitInv L D` carries them
from step to step.

`implements` and `run_initial` remain partial refinement theorems.  They classify every modeled
run that completes without exhausting Talos fuel.  A normally stopped native process returns
a status, which the compiled command passes to `proc_exit`.  The theorem preserves the ordered
effects and final world of those steps and the accepted or rejected exit request.  A permitted
guest resource trap matches a native process
prefix and residual action.  `run_initial` establishes this result from the modeled initial
store.  `bytes` combines the execution statement with encoding, exact decoding, and binary
validity.

The compiled refinement requires a host satisfying the WASI specification, the allocator
invariant with an empty free list, valid static bytes, and a memory cap of at most 65,535 pages.
[The WASI manual](../../docs/wasi.md) states the host, engine, and file-emission assumptions.
The generic
[total-process theorem](../../Verified/Wasi/ProcessTotalCorrect.lean) uses an application-supplied
well-founded progress relation, step charges with room for the copies of the state, and final-exit
acceptance.

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
compares native and Wasmtime output and status, checks interactive output before EOF, and checks
the exit status after a read error from a directory and, where `/dev/full` exists, a write error
from `/dev/full`.
