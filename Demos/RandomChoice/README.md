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
`LeanExe.Bytes.set`.  The loop's state carries the buffer, and each `Bytes.set` is the buffer's last
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

`pick_count` uses the fact that the accepted words form the interval [2^64 mod N, 2^64), whose
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
remain and exits with the errno of a write that fails.  The loop carries both buffers through its
state by moves: `random_get` fills the draw buffer, `putPicks` writes the output buffer in place,
and `writeAll` reads it in place, so a pass allocates nothing.

The status is the errno of `args`, 2 for a refused N or K, the errno of a failed `random_get` or
write, 78 when the writes of a pass took fewer bytes than offered until `writeAll`'s passes ran out,
77 when the loop's passes ran out with values still to choose, and 0 when the passes chose and
wrote K values.  Every errno lies from 0 to 76, so 77 and 78 differ from 2 and from every errno that
the run can return.  `verified_compile_wasi` writes a module that imports `fd_read`, `fd_write`,
`proc_exit`, `args_sizes_get`, `args_get`, and `random_get`.

## The command writes K values uniform on [1, N]

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

## Building, running, and testing

```sh
tests/random-choice/run.sh
build/tools/leanexe-wasmtime-host --arg choose --arg 6 --arg 10 run build/random-choice/command.wasm
tests/verified/run.sh --cases randomChoice
tests/native/verified.sh --module randomChoice
```

[The demo's driver](../../tests/random-choice/run.sh) checks the hashes of the reviewed
specifications and samples, builds the demo's modules, elaborates [the theorem
statements](../../tests/random-choice/Axioms.lean), which requires that each theorem use only the
three axioms, emits and validates the command's module, and runs it in the Wasmtime host.  The runs
with no argument, with N alone, with N or K of 0, and with letters, a sign, or a 20-digit value
above 2^64 in either place write nothing and exit with status 2.  The runs of `choose N K` for N
of 1, 6, `2^63 + 1`, at which `2^63 - 1` words of `2^64` are rejected, and `2^64 - 1`, with K up to
1,000,000, for `007 3`, and for `6 5 extra` exit with status 0 and write K lines, each a decimal
value without a leading zero in [1, N].  The run with N of 6 and K of 1,000,000 writes each of the
six values, the run with N of 1 writes only the value 1, and a run with standard output `/dev/full`
exits with status 51, `nospc`.  No run writes to stderr, and since the host draws its random bytes
from the operating system, no run checks the values beyond their range.  The driver prints
`random choice axiom check passed for 28 theorems` and `random choice: 21 runs passed`, with the
elapsed time and the maximum resident set of the run with N of `2^64 - 1` and K of 1,000,000.

The second command runs the module with N of 6 and K of 10, after the driver has written it.  It
writes ten lines, each a value from 1 to 6 in decimal, and exits with status 0.  On the AArch64
test host, three runs under `/usr/bin/time -v` with N = `2^64 - 1` and standard output in a file
took from 0.26 to 0.28 seconds for K = 1,000,000, with a maximum resident set of 16,024 to 16,752
KiB, and from 15,680 to 16,408 KiB for K = 1,000, so the resident set does not grow with K.

[The verified driver](../../tests/verified/run.sh) runs the 159 samples of [the verified
cases](../../Verified/Examples/Cases.lean), those of the pure core and of `putPicks`, in Wasmtime
against the specifications, and it checks [the file theorems](File.lean), which state that the
file that it writes holds the module.  [The native driver](../../tests/native/verified.sh) runs the
same cases on the module's translation to C, compiled with CompCert.  Each driver requires every
case to pass.

## Related examples

[The random-residue histogram](../RandomHistogram/README.md) draws random words in the same way,
and this demo reuses its `wordAt`, `words`, its lemmas on argument buffers and words, and its
shape of the command's theorems.  [The manifest checker](../ManifestCheck/README.md) carries one
read buffer through its loops in the same way.  [The byte update
examples](../../Verified/Examples/BytesSet.lean) count the allocations of `Bytes.set` in place and
of a copy, and [the running maximum](../../Examples/RunningMax/README.md) is a run of the
verified-request skill on words.

## References

- [Verified Compiler Manual](../../docs/verified-manual.md)
- [Verified WASI Manual](../../docs/wasi.md)
- [`Verified.Call`](../../Verified/Call.lean)
- [Mathlib `Nat.count_modEq_card`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/Int/CardIntervalMod.lean)
