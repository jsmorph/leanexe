# Binary64 running sum

`sumfp` reads numbers from stdin and prints a cumulative binary64 total after each line.
The initial total is positive zero.  Parsing and each addition round to nearest with ties to
even.  Digits, lengths, indices, transfer counts, and statuses use `UInt64`.  The total uses
`Float`.

## Input and output

The program accepts [the parser's general grammar](../../Library/Numerics/Decimal/ParseFloat/README.md#grammar):
decimal and hexadecimal numbers, optional signs, infinities, and NaNs.  Hexadecimal inputs require
a binary exponent.  The whole line must match.  Whitespace and NaN payloads are invalid.
The program strips one trailing CR.  LF ends a line, and EOF ends a nonempty final line.

Output uses [the scientific printer](../../Library/Numerics/Decimal/PrintFloat/README.md#specification),
followed by LF.  Finite nonzero results use the shortest decimal that rounds back to the result,
with the printer's nearest-decimal and tie rules.  Positive zero prints as `0e0`, negative zero
as `-0e0`, infinities as `Infinity` or `-Infinity`, and NaN as `NaN`.  A first input line containing
`-0` produces `0e0` because the initial total is positive zero.

| Input lines | Output lines |
|---|---|
| `12`, `-5`, `20` | `1.2e1`, `7e0`, `2.7e1` |
| `0.1`, `0.2`, `-0.3` | `1e-1`, `3.0000000000000004e-1`, `5.551115123125783e-17` |
| `1e16`, `1`, `-1e16` | `1e16`, `1e16`, `0e0` |
| `Infinity`, `-Infinity`, `1` | `Infinity`, `NaN`, `NaN` |

The process reads chunks of at most 4,096 bytes, retains a partial line across reads, and finishes
pending output before processing the next line.  Short writes retain the unwritten suffix.
Successful zero-byte writes retry that suffix.  Each completed line produces output before the
next blocking read.  Invalid input exits with status 28 and preserves preceding output.  A
returned I/O error stops the Wasm module with its errno as the exit status.  The native executable
raises the error as a Lean `IO.Error`, prints it, and exits with status 1.  Host traps preserve
committed effects.

## Specification and proofs

The [arithmetic specification](ArithmeticProof.lean) defines `lineBits` as the canonical binary64
rounding of the number denoted by a line.  `prefixBits` applies `Wasm.IEEE64.add` sequentially,
starting with the positive-zero word.  It includes rounding, cancellation, subnormals, overflow,
signed zero, infinities, and canonical NaNs.

| Module | Contents |
|---|---|
| [Numeric operations](Program.lean) | CR removal, the existing general binary64 parser, and scientific rendering with LF. |
| [Arithmetic correspondence](ArithmeticProof.lean) | Parser acceptance and bits, binary64 addition, and renderer properties. |
| [Stream process](Stream.lean) | Buffered input, partial lines, pending output, EOF, and error handling. |
| [Stream view](StreamView.lean), [kernel](Kernel.lean), and [termination](Termination.lean) | The relation between the process and [the shared stream process](../StreamFold/README.md), the line kernel's specification, and the progress of each step. |
| [Line model](Model.lean) | `ShortLines`, the line rooms that it implies, and the outputs and status of the kernel's fold over the input lines. |
| [Line limit](Limits.lean) | `InputLimits L`, the kernel specification `limitSpec L`, the invariant `LimitInv L` of the reached states, and the sizes of every state that a step returns. |
| [Action compilation](Wasi.lean) | Pure helper compilation and reflected effectful begin/step functions. |
| [Command module](Module.lean) | The unbounded Wasm loop, stack admission check, encoding, and validity proofs. |
| [Process refinement](Proof.lean) | Native-process correspondence, modeled initial store, `_start` partial refinement, and byte theorem. |
| [Printer charges](PrintCharges.lean) and [parser charges](ParseCharges.lean) | Bounds on the generated allocation bounds of the multiprecision arithmetic, the printer, and the parser, with the sizes of their arrays. |
| [Step charges](Charges.lean) | The charges of `begin` and of each step, and their bound for states within the limit. |
| [Stream correctness](StreamCorrect.lean) | `InputValues`, sequential binary64 output of the lines before the first rejected line, and source process termination. |
| [Compiled correctness](Correct.lean) | The charges derived from the limit, and eventual accepted exit with status 0 or 28 and the sequential binary64 output from the modeled initial store. |
| [Native executable](Native.lean) | The same process with the shared [POSIX fd 0 reader](../RunningSum/read.c) and flushed output streams. |

`InputValues input numbers status` holds when `numbers` are the numbers that the input lines
denote before the first line that denotes none, with `status` 0 when every line denotes a number
and 28 otherwise.  `inputValues_exist` and `inputValues_unique` show that every input with lines
shorter than `2^32` bytes determines one such pair.  `initial_terminates_fp` supplies, for every
such input whose lines up to and including the first line that denotes no number hold at most `L`
bytes, a Talos fuel threshold such that every larger fuel value runs the compiled command to
accepted exit with status `status` and the cumulative output of `numbers`.
`initial_terminates_fp_50000000` fixes `L` at 50,000,000, for which the memory inequality holds.
`fp_bytes` combines the theorem with encoding, exact decoding, and binary validity.  The theorem
starts with an empty event journal and output history and uses these premises:

| Premise | Requirement |
|---|---|
| [Line sizes](Model.lean) | `ShortLines` requires each line of the input to hold fewer than `2^32` bytes. |
| [Host progress](../StreamFold/StreamHost.lean) | `StreamHost` supplies successful transfers, input-prefix consumption, EOF, and committed output prefixes.  Each zero-byte write decreases a proof-only natural-valued credit, and a read or a write of at least one byte may set the credit to any value.  The Talos host also satisfies the WASI specification. |
| [Line limit](Limits.lean) | `InputLimits L` requires each line up to and including the first line that denotes no number to hold at most `L` bytes. |
| [Memory](Correct.lean) | `4096 + limitMemory L ≤ 65536 · 65535`, where `limitMemory L = 80 · L + 64,031,000`: the heap starts at 4,096 bytes, since the module has no byte literals, and the memory cap is 65,535 pages. |
| [Exit acceptance](Correct.lean) | `ExitAccepted` excludes rejected exits with status 0 or 28 at represented worlds. |

`limitCharges` derives from the limit the charges that the general theorem `terminates_fp` takes.
The process compacts its state after `begin` and after each step, so between steps the heap holds
the literal pool and one state, and each step needs room for its charge and the copies of the
state before and after it.  A copy of a state within the limit costs at most `8 · L + 4,305` bytes,
and a step from such a state at most `64 · L + 4,910,000` bytes, which include a parse of at most
`8 · L + 4,404,576` bytes, plus at most 59,112,378 bytes for one rendering.  `limitMemory L`
covers both copies and the step, as `limitMemory_room` proves:
`2 · (8 · L + 4,305) + 64 · L + 4,910,000 + 59,112,378 ≤ 80 · L + 64,031,000`.  Of the
rendering's bound, 59,109,312 bytes cover `shortest`, which computes at most 62 quotients with
`quotAt`, each at most 953,376 bytes.  `PrintFloatSteps.search_le` bounds the search for a finite
nonzero binary64 word at 27 steps below its start exponent, so it tests at most 28 exponents with
two quotients each, and the choice of the digits computes at most six more.

`implements` and `run_initial` classify modeled executions that complete without exhausting Talos
fuel.  They preserve ordered effects and terminal outcomes.  A permitted guest resource failure
matches a native prefix and residual action.  [The WASI manual](../../docs/wasi.md) states the
host, resource, engine, and file-emission assumptions.

The native executable reuses the integer application's descriptor reader.  It returns after one
successful POSIX `read`, retries interrupted calls, and propagates OS errors through Lean's
`IO.Error` API.  The native adapter, C compiler, operating-system streams, and Wasmtime's agreement
with the modeled floating-point and host semantics require external execution tests.

## Build and run

Commands run from the repository root.  [The host setup](../../docs/leanexe-manual.md#the-wasmtime-host)
provides the pinned Wasmtime host and its deterministic floating-point profile.

On an 8-CPU host with about 12 GiB of memory, the tested profile uses `LEANRUN_THREADS=3` and
`LEANRUN_MEMORY_HIGH=10G`, with a 12 GiB maximum.  The initial WASI compilation had a captured
memory peak of 4.84 GiB.  [The resource instructions](../../AGENTS.md#lean-process-limits)
describe these settings.

```sh
tests/running-sumfp/run.sh
printf '12\n-5\n20\n' | .lake/build/bin/running-sumfp-native
printf '12\n-5\n20\n' | build/tools/leanexe-wasmtime-host run build/running-sumfp/sumfp.wasm
```

[The application driver](../../tests/running-sumfp/run.sh) builds the proofs, audits their axioms,
checks fixed numerical outputs, exercises short and zero-byte transfers and committed failure
prefixes, compares native and Wasmtime output and status, checks interactive output before EOF,
and checks the exit status after read and write errors.  Its numerical cases cover parser rounding, sequential addition, cancellation, subnormals,
overflow, signed zero, NaNs, and infinities.

| Execution backend | Coverage |
|---|---|
| Native numeric checks | Exact parsed words and printed bytes, including negative zero, subnormals, parser overflow, infinities, and NaNs. |
| Native process and Wasmtime | The 29-case corpus covers finite rounding, cancellation, subnormals, arithmetic overflow, signed zero, nonfinite values, input framing, and rejection.  Scripted native streams add transfer partitions and errors. |
| Talos | Eight cases in the same Float module cover split reads, short and zero-byte writes, committed error and trap prefixes, invalid lines, and exit rejection.  Numeric paths use signed zero, underflow to zero, infinities, and NaN propagation. |
| Interactive native and Wasmtime | Output before the next read and before EOF. |
| I/O errors in native and Wasmtime | A directory as stdin and, where it exists, `/dev/full` as stdout.  Wasmtime exits with WASI errno 31 or 51, and the native executable exits with status 1. |

[Talos's memory model](https://github.com/jsmorph/talos/blob/87e3aa5e8f6e6f3b3eb5e7e4c5aba43071002d47/interpreter/Interpreter/Wasm/Mem.lean)
represents bytes with a lookup function.  Each write wraps the previous function, so reads can
traverse the accumulated write history.  Printing a finite nonzero value performs repeated
multiprecision divisions and array writes.  The Talos group uses the shorter numeric paths to
test the stream protocol within its time limit.  The native/Wasmtime corpus and universal FP
proofs cover the finite arithmetic and printing paths.

The driver runs all groups by default.  `--native-wasm` selects numeric and native
stream tests, native/Wasmtime comparisons, and interactive tests.  `--talos-only` selects the
scripted Talos cases.  Both groups build and audit the proofs.  An optional case name after
`--talos-only` selects one case from [the scripted cases](../../tests/running-sumfp/Talos.lean).
