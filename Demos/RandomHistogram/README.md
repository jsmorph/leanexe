# Random-residue histogram

## Request, specification, review, and program

[The request](request.txt) asks for a command that takes an integer N > 0 on its command line, draws
N random numbers, and writes, for M from 0 to 9, the count of the numbers that are M mod 10, ten
numbers that sum to N.  The choices that the user approved fix the rest: a random number is a 64-bit
little-endian word of the bytes that `random_get` returns, the command draws at most 512 words a
call so that its memory stays constant, N is the first argument after the program name, written in
decimal digits with 1 ≤ N < 2^64, a refused argument writes nothing and ends with status 2, the
errno of a failed call is the status, and the output is ten lines of decimal counts.

The pure core has three functions, whose specifications [the specification](Spec.lean) states,
written and reviewed by the method of [the verified-request
skill](../../.claude/skills/verified-request/SKILL.md).  `parseSpec` reads N from the buffer that
WASI's `args_get` fills, in which each argument follows the program name and ends with a zero byte,
and returns 0, which no valid N equals, for a refusal.  `histogramSpec` counts the words of an array by their residue mod 10, each word read as an
unsigned integer.  `renderSpec` writes ten lines from the first ten elements of an array, in Lean's
decimal form of a natural number, each followed by the byte 10.  The specification's comment records
each choice that the request leaves open: the program name and the arguments after the first are
ignored, leading zeros are digits, the range test applies to the numeral's value, and a count is a
word.

Two fresh agents reviewed the specification against the request, as [the review](review.md)
records.  Neither found a disagreement.  The first asked for three corrections of the comment and
named inputs that no sample covered, and [the samples](Samples.lean) now cover them, 74 in all.  The
second named four classes that no sample covers, which the review lists.

[The program](Program.lean) holds the three functions in the verified compiler's dialect.
`parseN` reads the buffer once with a state of four parts: the zero bytes seen, the value of the
argument's digits, whether every byte so far is a digit and the value stays below `2^64`, and
whether the argument has a byte.  Before it adds a digit `d` to the value `v`, it tests whether
`10 v + d` stays below `2^64` through `2^64 - 1 = 10 · 1844674407370955161 + 5`, which needs no
wider word.  `histogram` folds `countWord` over the words from ten zero counts.  `render` pushes the digits of each count onto an array with `digitCount` and `digitByte` of [the
library's `Int64` text](../../Library/Numerics/Decimal/Int64Text/README.md) and builds the output
buffer from that array.  [The verified compilation](Compiled.lean) writes a module that exports
`parseN`, `histogram`, and `render` as functions 3, 5, and 9.

[The command](Command.lean) is `main : Action UInt64`.  It calls `args` and `parseN` and then a loop
of at most `N / 512 + 1` passes, each of which calls `randomGet` for `8 · min r 512` bytes, with `r`
the words still to draw, and adds the residues of the buffer's little-endian words to the counts
with `tally`.  It then writes `render` of the counts to stdout in one write.  The loop's state holds
the counts, which the compiled code updates in place, and the code releases each pass's buffer after
`tally` reads it, so the heap that a run uses does not grow with N.  `verified_compile_wasi` writes
a module of 7,381 bytes that imports `fd_read`, `fd_write`, `proc_exit`, `args_sizes_get`,
`args_get`, and `random_get`.

## The command writes the counts of N random words

| Theorem | Statement |
|---|---|
| `parseN_eq`, `histogram_eq`, `render_eq` | Each program equals its specification, `parseN_eq` for a buffer of fewer than `2^64` bytes ([the proof](Proof.lean)). |
| `histogramSpec_sum` | The counts of `histogramSpec ws` sum to `ws.size` when `ws.size < 2^64`. |
| `parseN_callSpec`, `histogram_callSpec`, `render_callSpec` | `Verified.CallSpec compiled.module compiled.tables K spec compiled.f.bound` for `K` = 3, 5, and 9: called with a borrowed argument from a ready store with room for the bound, the function returns the specification's value without a trap and leaves a ready store ([the compilation](Compiled.lean)). |
| `parseN_bound`, `histogram_bound`, `render_bound` | The generated bounds are 0, 136 bytes, and at most 17,136 bytes. |
| `exec_main` | Under every host, every run of `main` followed by its exit that ends with the status `code` has the events `events ++ [.exit code]`, where `events` meet `Meets`, and `code` is at most 76 ([the command's proof](CommandProof.lean)). |
| `start_ends` | For every host, every host environment that satisfies `hostSpecWith host command.sysCalls`, and every world, every run of `_start` from the command's initial store with enough fuel ends as `Ends` states ([the compiled command](CommandStart.lean)). |
| `total_meets` | Under the premises of the generated `command.total` as well, a budget that fits the initial store's free memory and bounds the heap of every prefix of `main`, and a host that traps nowhere along `main` and its exit, every such run ends with the accepted exit after events that meet `Meets`. |

The theorems of the table use only `propext`, `Classical.choice`, and `Quot.sound`.  `Meets` of
[the command's specification](CommandSpec.lean) states the request over the events of a run, which
record each call and the host's reply.  The events start with those of a call of `args` that
returned `a`.  When `a.errno` is not 0, it is the status, and no other event follows.  When
`parseSpec a.bytes` is 0, the status is 2, and no other event follows.  Otherwise, with `N =
parseSpec a.bytes`, the events continue with the calls of `random_get` that `Draws N` states, each
for `8 · min r 512` bytes, until N words are drawn or a call returns an errno.  An errno ends the run
with that errno as the status and no write.  When every call returns errno 0, the returned bytes
hold exactly N words `w`, the counts of `histogramSpec w` sum to N, and the last event is one write
to stdout of `renderSpec (histogramSpec w)`, whose errno is the status.  The statement covers every
reply that the host's contracts allow, errnos of `args_sizes_get`, `args_get`, `random_get`, and the
write included.

`start_ends` composes `exec_main` with the generated `command.start`.  A run of `_start` ends in one
of three ways: (a) the accepted exit, after events that meet `Meets`; (b) a trap of the host or an
exit that the host rejects, after the events of a run of `main`; or (c) a trap of the guest at
`unreachable`, after a prefix of `main`.  The status of an accepted exit is at most 76, below the
126 at which Wasmtime 44 rejects an exit.  The theorem admits the guest's trap because the generated
theorem without it, `command.total`, takes a budget that bounds the heap that every prefix of
`main` allocates, and the resource model charges each pass of the loop for its buffer and credits
no release, so the charge grows with the number of passes and no budget covers every N.
`total_meets` takes such a budget as a premise, with a host that traps nowhere along the run, and
excludes (b) and (c).  A host may commit fewer bytes than the write offers, and the write's event records the count that it
committed.  The status is then the write's errno, 0 when the write succeeded.

The proof follows `main`.  A returned `args` result holds fewer than `2^32` bytes, the size that the
reporter's four-byte word gives (`args_returned`), so `parseN` computes `parseSpec` on it.
`draw_loop` proves by induction on the passes that the loop makes the calls of `Draws` and that its
counts are the fold of `countWord` over the drawn words, since `tally` counts the words that
`wordAt` reads by Horner's rule (`tally_eq`, `wordAt_eq`) and a buffer of whole words adds its words
to those before it (`words_append`).  The fold from ten zero counts is `histogram` of the words
(`histogram_list`), and `histogram_eq` and `render_eq` give the specification's output.

## Building, running, and testing

```sh
tests/random-histogram/run.sh
build/tools/leanexe-wasmtime-host --arg histogram --arg 1000000 \
  run build/random-histogram/command.wasm
tests/verified/run.sh --cases randomHistogram
tests/native/verified.sh --module randomHistogram
```

[The demo's driver](../../tests/random-histogram/run.sh) checks the hashes of the reviewed
specification and samples, elaborates [the theorem statements](../../tests/random-histogram/Axioms.lean)
and requires the three axioms, emits and validates the command's module, and writes its AArch64
Linux executable of 69,632 bytes with `a64-wasi wasm`, which fails when `genWasiElf` rejects the
module.  It then runs the module in the Wasmtime host.  The runs with no argument, `0`, `abc`, `-5`,
and `99999999999999999999` write nothing and exit with status 2.  The runs with N of 1, 9, 10, 512,
513, 1,000, and 1,000,000 exit with status 0 and write ten decimal counts that sum to N.  It prints
`random histogram axiom check passed for 14 theorems`, the executable's size, and `random histogram:
12 runs passed`.  The second command writes ten counts near 100,000, such as `100037`, `99394`, and
`99853`, in about 0.1 s on an AArch64 host.  The same command with N of 1,000,000,000 exits with
status 0 after 51 s with a resident set of 18 MB, and its counts sum to N.  Its 1,953,125 passes
would need about 8 GB if each kept its buffer of 4,096 bytes, more than the module's linear memory
of at most 4 GiB holds.  [The verified driver](../../tests/verified/run.sh) runs
the 74 samples of [the verified cases](../../Verified/Examples/Cases.lean) in Wasmtime against the
specifications, and each case of `histogram` and `render` requires two blocks to stay allocated
after the call, the argument's and the result's.  [The native driver](../../tests/native/verified.sh) runs the same cases on the
module's translation to C, compiled with CompCert, and `tests/baremetal/verified.sh --module
randomHistogram` runs them on that translation under QEMU without an operating system.  All 74 pass
in each.

## Related examples

[The flat call example](../../Verified/Examples/WasiSys.lean) calls `args` and `randomGet` in a
command, and [its total theorem](../../Verified/Examples/WasiSysTotal.lean) bounds the copies of the
argument bytes.  [The readAll message corollary](../../Verified/Examples/WasiReadAllMessage.lean)
states the output and status of a command over the events of every run, as `exec_main` does.
[The running maximum](../../Examples/RunningMax/README.md) is a run of the verified-request skill on
words, and [the ranked-choice tabulator](../Rcv/README.md) states call theorems over buffers.

## References

- [Verified Compiler Manual](../../docs/verified-manual.md)
- [Verified WASI Manual](../../docs/wasi.md)
- [`Verified.Call`](../../Verified/Call.lean)
- [WASI Preview 1 declarations](https://github.com/WebAssembly/WASI/blob/fae981bae14809d91f9bc2d63852d461f331d161/preview1/witx/wasi_snapshot_preview1.witx)
