# Unbiased random choice

## Request, specification, review, and program

[The request](request.txt) asks for an unbiased random choice by rejection sampling, with a theorem
that every output value has the same number of accepted words.  The plan fixes the interface:
`choose N K` takes N and K in decimal, with 1 ≤ N < 2^64 and 1 ≤ K < 2^64, and writes K lines, each
the decimal of an integer uniform on [1, N].  A refused argument writes nothing and ends with status
2, and the errno of a failed call is the status.  The plan also fixes the method: the command draws
64-bit little-endian words with `random_get`, at most 512 a call, accepts a word w when
w ≥ 2^64 mod N, which `(0 - N) % N` computes in word arithmetic, and outputs (w mod N) + 1.  The
command's memory must not depend on N or K, which [the request of `putPicks`](picks-request.txt)
states: the loop carries a draw buffer and an output buffer through its state, `random_get` fills
the first, and the picks are written into the second.

The pure core has three functions, whose specifications [the specification](Spec.lean) states,
written and reviewed by the method of [the verified-request
skill](../../.claude/skills/verified-request/SKILL.md).  `parseSpec` reads argument `i` from the
buffer that WASI's `args_get` fills, in which each argument follows the program name and ends with
a zero byte, and returns 0, which neither N nor K may equal, for a refusal.  `pickSpec (n, w)`
accepts w when n ≥ 1 and w ≥ 2^64 mod n and then gives (w mod n) + 1, and gives 0 for a rejected
word.  `renderSpec` writes one line for each element of an array, in Lean's decimal form of a
natural number, each followed by the byte 10.  The specification's comment records each choice
that the request leaves open: argument 0 is the program name, arguments after K are ignored,
leading zeros are digits, the range test applies to the numeral's value, and N = 0 accepts no word,
since [1, 0] holds no integer.

[The specification of `putPicks`](PicksSpec.lean), written and reviewed by the same method, states
the function that the command calls once for each draw.  `putPicksSpec (out, n, draw, limit)` is
`out` with its bytes from position 0 replaced by the lines of the first `limit` values that the
little-endian words of `draw` give, its size kept, the number of bytes of those lines, and the
number of values.  Its comment records the choices that the request leaves open: bytes after the
last whole word give no word, the values come in the order of the words, the bytes of `out` after
the lines keep their values, and lines longer than `out` lose their bytes past its end.

Two fresh agents reviewed each specification against the request, as [the review](review.md)
records.  None found a disagreement.  For the pure core, the first review asked for three
corrections of the comment and named inputs that no sample covered, and [the samples](Samples.lean)
now cover them, 132 in all.  For `putPicks`, the first review asked for four changes of the comment
and named six classes that no sample covered, and [its samples](PicksSamples.lean) now cover them,
27 in all.  The second reviews named classes that no sample covers and notes on the comments, which
the review lists with their responses.

[The program](Program.lean) holds the functions in the verified compiler's dialect.  `parseArg`
reads the buffer once with a state of four parts: the zero bytes seen, the value of the argument's
digits, whether every byte so far is a digit and the value stays below `2^64`, and whether the
argument has a byte.  `pick` tests `n != 0 && (0 - n) % n ≤ w` and returns `w % n + 1`.  `render`
computes the size of its text, `textSize`, builds an array of that many words, and writes each
value's digits and newline into it with `putLine`, in place.  `putPicks` runs a loop over the words
of the draw, which the random histogram's `wordAt` reads, whose state is the output buffer, the
position after the lines written, and the number of picks.  For each accepted word below the limit
it writes the line of the word's pick with `putLineBytes`, which writes each byte with
`LeanExe.Bytes.set`.  The loop's state holds the buffer, and each `Bytes.set` is the buffer's last
use, so the compiled code writes into the buffer's block.  [The verified compilation](Compiled.lean)
writes a module that exports `parseArg`, `pick`, `render`, and `putPicks` as functions 3, 4, 9, and
12.

## The pure core computes its specification

| Theorem | Statement |
|---|---|
| `parseArg_eq`, `pick_eq`, `render_eq` | Each program equals its specification, `parseArg_eq` for a buffer of fewer than `2^64` bytes and `render_eq` for an array of fewer than `2^59` values ([the proof](Proof.lean)). |
| `putPicks_eq` | `putPicks` equals `putPicksSpec` on every draw of fewer than `2^32` bytes ([the proof of `putPicks`](PicksProof.lean)). |
| `parseArg_callSpec`, `pick_callSpec`, `render_callSpec` | `Verified.CallSpec compiled.module compiled.tables K spec compiled.f.bound` for `K` = 3, 4, and 9: called with a borrowed argument from a ready store with room for the bound, the function returns the specification's value without a trap and leaves a ready store ([the compilation](Compiled.lean)). |
| `putPicks_implements` | `Verified.ImplementsA` of function 12 for `putPicksSpec`, with the output buffer as `Moved LeanExe.Bytes`: the function consumes the buffer that the caller moves to it and returns the specification's value without a trap. |
| `parseArg_bound`, `pick_bound`, `render_bound`, `putPicks_bound` | The generated bounds are 0, 0, at most `189 · values.size + 112` bytes, and 0. |

The theorems of the table use only `propext`, `Classical.choice`, and `Quot.sound`.  `parseArg`'s
loop over the buffer is a fold of `parseStep index` over its bytes, which counts the zero bytes and,
over an argument without a zero byte, computes the specification's value and decides whether the
argument is a numeral below `2^64` (`fold_argument`), and `fold_parse` proves the equation by
induction on the zero bytes before the argument.  `pick_eq` follows from `0 - n = 2^64 - n` and
`(2^64 - n) mod n = 2^64 mod n`, and `render`'s fold writes the words of each value's line after
those of the values before it (`putLine_get`, `fill_fold`) into an array of `textSize` words
(`textSize_eq`).  `putPicks_eq` follows the loop of `putPicks` with the invariant that after `k`
words the buffer holds the lines of the first values of those words, at most `limit`, followed by
the bytes of `out` after them, and `putLineBytes_getD` gives the bytes that `Bytes.set` writes.

## The choice of each value has the same number of words

| Theorem | Statement |
|---|---|
| `pick_count` | For every N and every v with 1 ≤ v ≤ N, exactly `⌊2^64 / N⌋` words w are accepted and give v ([the counting theorems](Unbiased.lean)). |
| `picks_count` | For every K and every sequence o of K values in [1, N], exactly `⌊2^64 / N⌋^K` sequences of K accepted words give o. |
| `output_count` | For every K and every sequence o of K values in [1, N], exactly `⌊2^64 / N⌋^K` K-tuples of accepted words make `main` write the lines of o, and `output_count_outside` gives no K-tuple for a sequence with a value outside [1, N] ([the output](Output.lean)). |
| `accepted_count`, `accepted_half` | N ≥ 1 accepts `2^64 - (2^64 mod N)` words, `N · ⌊2^64 / N⌋`, and at least `2^63`. |
| `short_count` | For N ≥ 1 and M ≥ 4 K + 1024, at most `2^(64 M - 512)` of the `2^(64 M)` sequences of M words hold fewer than K accepted words. |

The counting theorems assume no probability.  When the host's words are independent and uniform
on [0, 2^64), `picks_count` and `accepted_count` give a sequence of K accepted words the picks o
with probability `⌊2^64 / N⌋^K / (N · ⌊2^64 / N⌋)^K = N^(-K)`.  The output of a run with status 0
is the picks of the first K accepted words, and those words are independent and uniform on the
accepted set, since whether a word is accepted depends on that word alone, so the output is
uniform on [1, N]^K.  No theorem states that last step, which conditions on the run's status and
on the positions of the accepted words.  Under the same assumption, `accepted_half` makes each word
accepted with probability at least 1/2, and `short_count` bounds by `2^-512` the probability that
M words hold fewer than K accepted ones.

`pick_count` counts the words of each residue in the accepted interval [2^64 mod N, 2^64), whose
length is `N · ⌊2^64 / N⌋`.  Mathlib's `Nat.count_modEq_card` counts the naturals below a bound that
have a given residue, and its counts below `2^64` and below `2^64 mod N` differ by `⌊2^64 / N⌋` for
every residue c < N (`residue_count`).  `short_count` bounds the count by the exponential moment:
the sum over the sequences of `3^r`, with r a sequence's number of rejected words, is the M-th power
of the sum over one word, `2^64 + 2 R ≤ 2^65` for R ≤ `2^63` rejected words, and a sequence with
fewer than K accepted words has `r ≥ M - K + 1`, so the count is at most
`2^(65 M) / 3^(M - K + 1)`, at most `2^(64 M - 512)` when M ≥ 4 K + 1024.  `output_count` follows
from `picks_count` and `renderSpec_inj`: the digits of a value hold no byte 10 and determine the
value, so the lines of two sequences are equal only when the sequences are.

## The command

[The command](Command.lean) is `main : Action UInt64`.  It calls `args` and `parseArg` for N and K
and then a loop of at most `passes K = K / 128 + 3` passes, while values remain and no pass has
set a status: the errno of a failed call, or 78 for a stalled write.  The loop's state is the
values still to choose, the status of a failed call, a draw buffer of 4,096 bytes, and an output
buffer of 10,752 bytes, which hold the lines of 512 values of at most 20 digits.  Each pass draws
512 words into the whole draw buffer with `randomGet`, writes the lines of the picks of their
accepted words, at most the values that remain, into the output buffer with `putPicks`, and writes
the window of the output buffer that those lines fill with `writeAll` of [the shared write
loop](../../LeanExe/Wasi/WriteAll.lean), which follows a short write with a write of the bytes that
remain and exits with the errno of a write that fails.  The loop keeps both buffers in its state
and moves them from pass to pass: `random_get` fills the draw buffer, `putPicks` writes the
output buffer in place, and `writeAll` reads it in place, so a pass allocates nothing.

The status is the errno of `args`, 2 for a refused N or K, the errno of a failed `random_get` or
write, 78 when the writes of a pass took fewer bytes than offered until `writeAll`'s passes ran out,
77 when the loop's passes ran out with values still to choose, and 0 when the passes chose and
wrote K values.  Every errno lies from 0 to 76, so 77 and 78 differ from 2 and from every errno that
the run can return.  `verified_compile_wasi` writes a module that imports `fd_read`, `fd_write`,
`proc_exit`, `args_sizes_get`, `args_get`, and `random_get`.

## The command writes the picks of the first K accepted words

| Theorem | Statement |
|---|---|
| `exec_main` | Every run of `main` followed by its exit, under every host, that ends with the exit status `code` has events that meet `Meets` followed by the exit, and `code` is at most 78 ([the command's proof](CommandProof.lean)). |
| `meets_output` | The events of a run that meet `Meets` with status 0 start with a run of `args` that returns N and K, both nonzero, and write `outputOf N chosen` to standard output, for the K-tuple `chosen` of the first K accepted words that the passes drew ([the output](Output.lean)).  With `exec_main` and `output_count`, it gives the count of the request: for every K and every sequence o of K values in [1, N], exactly `⌊2^64 / N⌋^K` K-tuples of accepted words make `main` write the lines of o. |
| `start_ends` | For every host, every host environment that satisfies `hostSpecWith host command.sysCalls`, and every world, every run of `_start` with enough fuel ends with the accepted exit after events that meet `Meets`, with a trap of the host or a rejected exit, or with a trap of the guest at `unreachable` after a prefix of `main` ([the command's theorem](CommandStart.lean)). |
| `total_meets` | Under the premises of the generated `command.total`, a budget that fits the free memory and bounds the heap of every prefix of `main`, and a host that traps nowhere along `main` and its exit, every run ends with the accepted exit after events that meet `Meets`. |
| `cap_count` | At most a `2^-512` part of the sequences of the `512 · passes K` words of the cap's passes hold fewer than K accepted words, from `short_count`, since `512 · (K / 128 + 3) ≥ 4 K + 1024`.  It counts tuples of words with `accepts`, and no theorem relates them to the list of words that `Meets` gives a run at the cap. |

The theorems of the table use only `propext`, `Classical.choice`, and `Quot.sound`.
`Meets host world events code` states the events of `args`, the status 2 for a refused N or K with
no other event, and otherwise the passes of `Rounds`: each pass calls `random_get` for 4,096 bytes
and writes `passText`, the lines of the picks of the pass's accepted words, at most the values that
remain, with the writes of `Writes`, each of which offers the bytes not yet written.  The status is
0 exactly when the passes chose K values and wrote them, and then the bytes written to standard
output are `renderSpec` of the first K picks of the accepted words that the passes drew.  A run
whose passes reach the cap ends with status 77 after drawing `512 · passes K` words of which fewer
than K are accepted.

The proof follows `main`.  A returned `args` result has a buffer of fewer than `2^32` bytes, so
`parseArg` computes `parseSpec` on it.  A call of `random_get` that returns errno 0 fills the whole
draw buffer with the reply's 4,096 bytes (`splice_whole`), so `putPicks` writes the lines of the
picks of the reply's accepted words, at most the values that remain, which `pass_put` derives from
`putPicks_eq`, and the window of the output buffer from position 0 that the count of bytes names
holds those lines.  The loop of `writeAll` makes the writes of `Writes` (`writes_of_run`), and the
loop of `main` makes the passes of `Rounds` (`draw_loop`).  `Rounds.output` gives the bytes written
by passes that end with status 0, and `Rounds.cap` the words of passes that reach the cap.

## Memory

| Theorem | Statement |
|---|---|
| `body_bounded` | Every run and every prefix of `main`'s body charges at most `budget`, 6,306,448 bytes, for every N and K, under every host whose successful `args_sizes_get` replies ask for at most `argsLimit` bytes ([the budget](Budget.lean)). |
| `initial_within`, `total_meets_every` | The budget fits the free memory of the command's initial store, and for every N and K, under every such host that traps nowhere along `main` and its exit, every run of `_start` from that store ends with the accepted exit after events that meet `Meets`, from `total_meets` with `body_bounded` and `initial_within`. |

The resource model charges a copy of an owned value at each use after which the value stays live,
and it credits no release.  `budget` holds the block of `args`, 6,291,504 bytes, at the random
histogram's limit `argsLimit`, and the loop's initial draw buffer and output buffer, 4,144 and
10,800 bytes with their headers.  A pass charges nothing: the call of `random_get` takes the draw
buffer's variable, which dies there, without a copy, `putPicks` takes the output buffer as owned
and has a generated bound of 0, and `writeAll` borrows the output buffer and charges nothing in
each of its passes.  The proof of `body_bounded` bounds the loop with a charge of 0 for each pass,
so the budget does not depend on N or K, and the statement bounds the whole body.

## The native executable writes the picks of the first K accepted words

`genWasiElf` writes the command's AArch64 Linux executable of 69,632 bytes from the module, with
the shim's stubs for the stream functions, `args_sizes_get`, `args_get`, and `random_get`, and a
linear memory of 4,096 pages.  `tests/linux/a64-wasi.sh` writes it as `choice.elf` and elaborates
the theorems of the file beside it, and the demo's driver writes it from the same module with the
same commands as `build/random-choice/command.elf` and runs it.  The theorems of the next table lie
in [the executable's theorems](../../tests/TestSupport/A64/ImageFilesRandomChoice.lean), [the
footprints](Native.lean), and [the corollary under the shim](NativeChoices.lean).

| Theorem | Statement |
|---|---|
| `choice_elf_file`, `choice_elf_segments`, `choice_elf_layout`, `choice_elf_entry`, `choice_elf_room` | The file's bytes are those that `genWasiElf` gives for the command's module, its program headers are those of the generator's layout, its entry is the shim's prefix, and the stack's room holds the module's stack bound. |
| `choice_elf` | For every reply sequence, a process that Linux's loader started from the file reaches `exit_group`, and its trace holds the layer events of a run of `main` and its exit under the shim's host with the process's arguments: an accepted exit, whose status X0 holds, a rejected exit, a trap of the shim, or a guest trap after a prefix. |
| `linux_footprint_bounded` | Under the shim's host, for every N and K, with arguments whose strings and eight-byte pointers take at most `argsLimit` bytes, and at a cap of at most 65,535 pages that holds `budget` above byte 4,096, every run of `_start` with enough fuel ends without a guest trap. |
| `linux_exec_choices` | Under the shim's host, with arguments whose strings and eight-byte pointers take at most `argsLimit` bytes, a run of `main` and its exit whose layer events meet `Full` ends at the accepted exit, and its status and layer events meet `Choices`. |
| `choice_elf_choices` | For every reply sequence and every N and K, a process started from the file with arguments whose strings and eight-byte pointers take at most `argsLimit` bytes reaches `exit_group` with layer events that hold the replies, and when they meet `Full`, X0 and the events meet `Choices`. |
| `witness_run`, `choice_elf_witness` | The premises of `choice_elf_choices` and `Full` hold together: for the replies `witnessReplies`, the arguments `c`, `1`, and `1`, and a process `witnessProc` that holds the file and the initial stack, the process reaches `exit_group` with X0 at 0 after layer events that meet `Full` and `Choices`. |

The random histogram's `Full ls` holds when every `getrandom` of the layer events `ls` returned the
count that it asked for and every `write` returned an error number or at most the count of bytes
that it offered, and its `randomData ls` collects the bytes that the `getrandom` events returned.
`Mirrors x e` states that the layer event `e` is the one event that the shim makes for the WASI
event `x` of such a run.  For a `random_get` of 4,096 bytes, `e` is a `getrandom` of 4,096 bytes
with flags 0 that returned 4,096, whose output region holds the bytes of the call's reply, and for
a write to standard output, `e` is a `write` of descriptor 1 whose input holds the write's bytes and
whose result is the write's count, at most the bytes offered, or an error number whose WASI errno
is the write's.  No layer event mirrors any other WASI event.

`Choices args ls status` states the layer events and the status that the request asks of such a
run, with N and K the values that `parseSpec` reads from arguments 1 and 2 (`argN`, `argK`).  When
`parseSpec` refuses N or K, no layer event precedes `exit_group`, and the status is 2.  Otherwise
the layer events mirror, one for one, WASI events that make the passes of `Rounds` from K values
and `passes K` passes, whose random bytes are `randomData ls` and whose status is the run's.  Each
pass is therefore a `getrandom` of 4,096 bytes followed by `write` calls, each of which offers the
bytes of the pass's lines that the writes before it did not take.  The status is 0 only when the
bytes that the writes took, `Linux.writeData 1 ls`, are `outputOf N chosen` for the K-tuple
`chosen` of the first K accepted words of `randomData ls`, and 77 only when `randomData ls` holds
the `512 · passes K` words of the cap's passes, fewer than K of them accepted.  `Rounds` gives the
other statuses: 78 when the writes of a pass stalled, and the errno of a `write` that returned an
error number.  With `output_count`, the status-0 case gives the count of the request for the
executable: for every K and every sequence o of K values in [1, N], exactly `⌊2^64 / N⌋^K` K-tuples
of accepted words make the process's writes take the lines of o.

Linux's `write` returns an error number or at most the count that it was given (write(2)), so the
condition on writes holds for every run.  getrandom(2) guarantees every byte of a read of up to 256
bytes once the urandom source is initialized, and Linux 6.12's `get_random_bytes_user` returns
every byte of a read of at most a page unless the copy faults.  Each of the command's reads asks
for 4,096 bytes.  [The random histogram's guide](../RandomHistogram/README.md#the-native-executable-writes-the-counts)
gives the signals and the limits under which a write takes fewer bytes than it offers.

The proof composes the footprint with the command's theorems.  `linux_footprint_bounded` gives the
budget premise of the generated `command.start` from `body_bounded` through `call_prefix_bound`,
since the shim answers `args_sizes_get` with the count and size of the launch's arguments, and the
budget does not depend on N or K, so the corollary holds for every N and K.  `linux_exec_choices`
excludes the trapped runs.  Under a host that rejects no exit status below 126, as the shim does,
the loop of `main` traps only at a trapped `random_get` of 4,096 bytes or a trapped write
(`draw_loop`), so a trapped run of `main` has a trapped `args_sizes_get`, `args_get`,
`random_get`, or write (`main_trapped`), whose image no layer events that meet `Full` give (the
histogram's `image_untrapped`), and the exit of a status of at most 78 is accepted.  For the
accepted exit, `exec_main` gives `Meets`, and the images of the events of `Rounds` mirror them and
return the bytes that the passes drew (`rounds_mirrors`, from `random_mirror` and `write_mirror`).
The writes of the images took the bytes that the writes of `Rounds` committed
(`Images.writeData`), and `first_picks` gives the K-tuple of the first K accepted words.

`choice_elf_witness` gives the premises: a memory that holds the file's two segments below `2^32`
and the initial stack of `c`, `1`, and `1` at `2^32`, which `decide` checks byte by byte, and the
replies `witnessReplies`, which answer call 0 with 4,096 zero bytes and every later call with 2.
`witness_run` follows `main` under those replies: `args` returns the arguments, N and K are 1, the
one `getrandom` asks for 4,096 bytes and returns them (`witness_random`), `putPicks` writes the line
`1` (`pass_put` and `witness_text`), the one write offers its 2 bytes and takes both
(`witness_write`), no value remains (`witness_loop`), and the run exits with status 0.  The kernel
evaluates no run of the executable: the footprint theorem gives the process's run, and the proof
reasons over its events.

## Building, running, and testing

```sh
tests/random-choice/run.sh
build/tools/leanexe-wasmtime-host --arg choose --arg 6 --arg 10 run build/random-choice/command.wasm
build/tools/leanexe-wasmtime-host --random-bytes build/random-choice/fixed/largest.bytes \
  --arg choose --arg 18446744073709551615 --arg 4 run build/random-choice/command.wasm
build/random-choice/command.elf 6 10
qemu-aarch64 build/random-choice/command.elf 6 10
tests/linux/a64-wasi.sh
tests/verified/run.sh --cases randomChoice
tests/native/verified.sh --module randomChoice
```

[The demo's driver](../../tests/random-choice/run.sh) checks the hashes of the reviewed
specifications and samples, builds the demo's modules, elaborates [the theorem
statements](../../tests/random-choice/Axioms.lean), which requires that each theorem use only the
three axioms, emits and validates the command's module, and writes its executable with
`a64-wasi wasm`, which fails when `genWasiElf` rejects the module.  It then runs the command in the
Wasmtime host, on the host's processor, which must be AArch64 Linux, and under `qemu-aarch64`.
`RUNNERS` selects among the three, and `BUILD=no` runs the module and the executable that an
earlier run wrote, without Lean.  In each runner, the runs with no argument, with N alone, with N
or K of 0, and with letters, a sign, or a 20-digit value above 2^64 in either place write nothing
and exit with status 2.  The runs of `choose N K` for N of 1, 6, `2^63 + 1`, at which `2^63 - 1`
words of `2^64` are rejected, and `2^64 - 1`, with K up to 1,000,000, for `007 3`, and for
`6 5 extra` exit with status 0 and write K lines, each a decimal value without a leading zero in
[1, N].  The run with N of 6 and K of 1,000,000 writes each of the six values, the run with N of 1
writes only the value 1, and a run with standard output `/dev/full` exits with status 51, `nospc`.
Natively and under QEMU, a run of `choose 6 1000` whose standard output appends to a file of 500
bytes under a file size limit of 512 bytes, with `SIGXFSZ` ignored, exits with status 22, `fbig`,
and leaves the file at 512 bytes, the last 12 of them digits and newlines.  No run writes to stderr.
These runs draw their random bytes from the operating system, so they check the values only for
their range.

In the Wasmtime host, the driver also runs the module with `--random-bytes FILE`, under which each
call of `random_get` takes the next bytes of FILE and returns errno 29, `io`, when fewer bytes
remain than it asks for.  [The expected outputs](../../tests/random-choice/Expected.lean) evaluate
`parseSpec`, `passPicks`, `passText`, `passes`, and `capStatus`, with the passes that `Rounds`
states, on each case's arguments and bytes, and check the clauses of `Meets` for status 0 and for
the cap.  Each run must write that output byte for byte and exit with that status, and `BUILD=no`
takes the expected outputs from an earlier run.  Each pass draws 4,096 bytes.  The cases are
`6 10`, whose first words are 0 to 3, which N of 6 rejects, and words near `2^64`;
`9223372036854775809 300`, N of `2^63 + 1`, which rejects the words below `2^63 - 1`, with words at
that bound and two passes; `6148914691236517206 50`, N of `⌊2^64 / 3⌋ + 1`, which rejects the words
below `N - 2`, with words at that bound and at N and 2N; `18446744073709551615 4`, whose values
include 1 and `2^64 - 1`; `1 600`, two passes of 512 and 88 values; `1000 2000`, four passes of
bytes of a fixed generator; `6 1` with three passes of zero bytes, which reach the cap with status
77 and write nothing; `6 200` with four passes of three accepted words each, which write 12 values
and reach the cap; `6 1000` with one pass and 100 more bytes, which writes the first pass's values
and exits with status 29; `6 1` with no bytes, status 29; and `0 5` with no bytes, a refusal with
status 2.

Natively, the driver runs the executable under strace and reads every `getrandom` and `write` with
its undecoded arguments.  The runs of `choose 6 1000` and `choose 18446744073709551615 100000` make
only `getrandom`, `write`, and `exit_group` calls.  Each `getrandom` passes the address of the
first, 4,096 bytes, and flags 0 and returns 4,096, and each `write` is of descriptor 1, offers the
bytes of its pass that the pass's earlier writes did not take, from the address of the run's first
write plus the bytes that they took, and returns its count, so each pass makes one write.  The
first run makes a `getrandom`, a write of 1,024 bytes, a `getrandom`, and a write of 976 bytes.
Under the file size limit, the first write offers 1,024 bytes and returns 12, and the second passes
the address plus 12, offers 1,012 bytes, and fails with `EFBIG`.  Two runs replace replies with
strace's injection.  When every `getrandom` of `choose 6 1000` returns 4,096 without filling the
buffer, the draw buffer keeps its zero bytes, which N of 6 rejects, and the run reaches the cap: ten
`getrandom` calls, the `passes` of K = 1,000, no write, and status 77.  When every `write` of
`choose 6 1` returns 0, the run makes three writes of its line's 2 bytes, the passes of `writeAll`,
and exits with status 78.  A run with `abc` makes only `exit_group`.  The driver prints
`random choice axiom check passed for 34 theorems`, the module's size, 5,851 bytes, the
executable's size, 69,632 bytes, and its SHA-256,
ce3a19326ee50a73b738542c649d7675602b2e82a9d9683cebc1d116a270e52d, and
`random choice: 82 runs passed`, with the elapsed time and the maximum resident set of the run with
N of `2^64 - 1` and K of 1,000,000 in each runner.

The second, fourth, and fifth commands run the module, the executable, and the executable under
QEMU's user-mode emulator with N of 6 and K of 10, after the driver has written them.  Each writes
ten lines, each a value from 1 to 6 in decimal, and exits with status 0.  The third command runs the
module on the bytes of the case `18446744073709551615 4` and writes `1`, `2`,
`18446744073709551615`, and `9223372036854775808`.  On the AArch64 test host,
three runs of the module under `/usr/bin/time -v` with N = `2^64 - 1` and standard output in a file
took from 0.26 to 0.28 seconds for K = 1,000,000, with a maximum resident set of 16,024 to 16,752
KiB, and from 15,680 to 16,408 KiB for K = 1,000, so the resident set does not grow with K.  The
executable's run with K = 1,000,000 on the same host, in a scope of one core, took 1.58 seconds
with a maximum resident set of 1,496 KiB.

`tests/linux/a64-wasi.sh` writes the executable from the module that `tools/Emit.lean` emits and
elaborates [the executable's theorems](../../tests/TestSupport/A64/ImageFilesRandomChoice.lean)
beside it, which requires the three axioms of each.

[The verified driver](../../tests/verified/run.sh) runs the 159 samples of [the verified
cases](../../Verified/Examples/Cases.lean), those of the pure core and of `putPicks`, in Wasmtime
against the specifications, and it checks [the file theorems](File.lean), which state that the
file that it writes holds the module.  [The native driver](../../tests/native/verified.sh) runs the
same cases on the module's translation to C, compiled with CompCert.  Each driver requires every
case to pass.

## Related examples

[The random-residue histogram](../RandomHistogram/README.md) draws random words in the same way,
and this demo reuses its `wordAt`, `words`, its lemmas on argument buffers and words, its `Full`,
`randomData`, and lemmas on the shim's images, and its shape of the command's and the executable's
theorems.  [The manifest checker](../ManifestCheck/README.md) keeps one
read buffer in the states of its loops in the same way.  [The byte update
examples](../../Verified/Examples/BytesSet.lean) count the allocations of `Bytes.set` in place and
of a copy, and [the running maximum](../../Examples/RunningMax/README.md) is a run of the
verified-request skill on words.

## References

- [Verified Compiler Manual](../../docs/verified-manual.md)
- [Verified WASI Manual](../../docs/wasi.md)
- [`Verified.Call`](../../Verified/Call.lean)
- [Mathlib `Nat.count_modEq_card`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/Int/CardIntervalMod.lean)
