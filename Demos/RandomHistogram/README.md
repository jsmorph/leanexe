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
`tally` reads it.  No theorem states that the heap of a run stays constant, since the resource
model credits no release, and no run tests it beyond N of 1,000,000.  `verified_compile_wasi`
writes a module of 7,381 bytes that imports `fd_read`, `fd_write`, `proc_exit`, `args_sizes_get`,
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
excludes (b) and (c).  A host may commit fewer bytes than the write offers, and the write's event
records the count that it committed.  The status is then the write's errno, 0 when the write
succeeded.

The proof follows `main`.  A returned `args` result holds fewer than `2^32` bytes, the size that the
reporter's four-byte word gives (`args_returned`), so `parseN` computes `parseSpec` on it.
`draw_loop` proves by induction on the passes that the loop makes the calls of `Draws` and that its
counts are the fold of `countWord` over the drawn words, since `tally` counts the words that
`wordAt` reads by Horner's rule (`tally_eq`, `wordAt_eq`) and a buffer of whole words adds its words
to those before it (`words_append`).  The fold from ten zero counts is `histogram` of the words
(`histogram_list`), and `histogram_eq` and `render_eq` give the specification's output.

## The native executable writes the counts

`genWasiElf` writes the command's AArch64 Linux executable of 69,632 bytes from the module, with
the stubs of the shim for the stream functions, `args_sizes_get`, `args_get`, and `random_get`, and
a linear memory of 4,096 pages.  `tests/linux/a64-wasi.sh` writes it as `histogram.elf` and
elaborates the theorems of the file beside it, and the demo's driver writes it from the same module
with the same commands as `build/random-histogram/command.elf` and runs it.  The theorems of the
next table lie in [the executable's theorems](../../tests/TestSupport/A64/ImageFilesRandomHistogram.lean),
[the charge of `main`](Budget.lean), [the footprints](Native.lean), and [the corollary under the
shim](NativeCounts.lean).

| Theorem | Statement |
|---|---|
| `histogram_elf_file`, `histogram_elf_segments`, `histogram_elf_layout`, `histogram_elf_entry`, `histogram_elf_room` | The file's bytes are those that `genWasiElf` gives for the command's module, its program headers are those of the generator's layout, its entry is the shim's prefix, and the stack's room holds the module's stack bound. |
| `histogram_elf` | For every reply sequence, a process that Linux's loader started from the file reaches `exit_group`, and its trace holds the layer events of a run of `main` and its exit under the shim's host with the process's arguments: an accepted exit, whose status X0 holds, a rejected exit, a trap of the shim, or a guest trap after a prefix. |
| `body_bounded`, `budget_fits`, `budget_full` | Every run and every prefix of `main`'s body charges at most `budget` under a host whose replies give an argument block of at most `argsLimit` bytes and an N of at most `drawLimit`, and `budget` fits the executable's 4,096 pages above the heap's start, with no room for one more pass. |
| `linux_footprint_bounded` | Under the shim's host, with arguments whose strings and eight-byte pointers take at most `argsLimit` bytes and whose N is at most `drawLimit`, and at a cap of at most 65,535 pages that holds `budget` above byte 4,096, every run of `_start` with enough fuel ends without a guest trap. |
| `linux_exec_counts` | Under the shim's host, with arguments whose strings and eight-byte pointers take at most `argsLimit` bytes, a run of `main` and its exit whose layer events meet `Full` ends at the accepted exit, and its status and layer events meet `Counts`. |
| `histogram_elf_counts` | For every reply sequence, a process started from the file with arguments whose strings and eight-byte pointers take at most `argsLimit` bytes and whose N is at most `drawLimit` reaches `exit_group` with layer events that hold the replies, and when they meet `Full`, X0 and the events meet `Counts`. |

`Full ls` holds when every `getrandom` of the layer events `ls` returned the count that it asked for
and every `write` the count of bytes that it offered.  `Counts args ls status` states the layer
events and the status that the request asks of a run whose calls succeed.  When `parseSpec` refuses
the arguments, no layer event precedes `exit_group`, and the status is 2.  Otherwise, with N the
value that `parseSpec` reads from the arguments, each followed by a zero byte, the events are calls
of `getrandom`, each of at most 4,096 bytes with flags 0, followed by one `write` of descriptor 1,
the bytes that `getrandom` returned hold exactly N little-endian words `w`, the counts of
`histogramSpec w` sum to N, the bytes written to descriptor 1 are `renderSpec (histogramSpec w)`,
and the status is 0.

Linux's replies meet `Full` when standard output is a regular file or a blocking pipe, no call
fails, and no write reaches a full disk or `RLIMIT_FSIZE`.  getrandom(2) guarantees every byte of a
read of up to 256 bytes once the urandom source is initialized, and Linux 6.12's
`get_random_bytes_user` returns every byte of a read of at most a page, which the command's reads of
at most 4,096 bytes are, unless the copy faults.  A write of at most `PIPE_BUF`, 4,096 bytes, to a
blocking pipe takes all of its bytes, and the command writes at most 210 (pipe(7)).  A write to a
regular file can take fewer bytes at a full disk or at `RLIMIT_FSIZE`, and `RLIMIT_FSIZE` and a
pipe whose reader closed raise signals that end the process before `exit_group` (write(2)).  Today
a short write ends the run with status 0 and part of the ten lines, since `main` writes once with
`writeStdoutSome`, whose errno is 0 for a short count, and `Meets` admits that run.

The corollary bounds N because the resource model charges each pass of the loop for the blocks that
it allocates and credits no release.  `drawLimit`, 12,839,935, is the largest N for which `budget`
fits the executable's memory: 6,291,504 bytes for the block of `args` and each of its seven copies,
408 bytes for three copies of the counts, at most 17,136 bytes for `render`, and 8,696 bytes for
each of the `N / 512 + 1` passes.  Linux 4.13 and later limit the strings and pointers of `argv`
and `envp` together to at most 6 MiB, `argsLimit` (`get_arg_page` of `fs/exec.c` in v4.13,
`bprm_stack_limits` in v6.12), so every process that Linux starts meets the premise on the
arguments.  A corollary for every N needs a resource model that credits every block that a pass
releases, the buffer and the copies of the counts and of the buffer, which changes the shared
definitions of `Verified/Wasi/` and needs a proof that the allocator reuses a released block.

The proof composes three parts.  `body_bounded` follows `main`'s reflected body with the rules of
`Verified/Wasi/ResourceRules.lean`, and `loop_bounded` bounds the loop's passes from counts of ten
words, which every pass keeps (`tally_size`), and `loop_kept` gives the counts of ten words after
the loop.  `linux_footprint_bounded` gives the budget premise of the generated `command.start` from
the shim's replies to `args_sizes_get` and `args_get`.  `linux_exec_counts` excludes the trapped
runs: a trapped run of `main` has a trapped `args_sizes_get`, `args_get`, `random_get`, or write
(`main_trapped`), whose image no layer events that meet `Full` give (`image_untrapped`), and an
exit of a status of at most 76 is accepted.  For the accepted exit, `exec_main` gives `Meets`, and
the images of its events give the calls of `getrandom` and the bytes that they returned
(`draws_full`) and the write and the bytes that it took (`write_full`).

## Building, running, and testing

```sh
tests/random-histogram/run.sh
build/tools/leanexe-wasmtime-host --arg histogram --arg 1000 run build/random-histogram/command.wasm
build/random-histogram/command.elf 1000
qemu-aarch64 build/random-histogram/command.elf 1000
tests/linux/a64-wasi.sh
tests/verified/run.sh --cases randomHistogram
tests/native/verified.sh --module randomHistogram
```

[The demo's driver](../../tests/random-histogram/run.sh) checks the hashes of the reviewed
specification and samples, elaborates [the theorem statements](../../tests/random-histogram/Axioms.lean)
and requires the three axioms, emits and validates the command's module, and writes its executable
with `a64-wasi wasm`, which fails when `genWasiElf` rejects the module.  It then runs the command in
the Wasmtime host, on the host's processor, which must be AArch64 Linux, and under `qemu-aarch64`.
The runs with no argument, `0`, `abc`, `-5`, `+5`, and `99999999999999999999` write nothing and
exit with status 2.  The runs with N of 1, 9, 10, 512, 513, 1,000, and 1,000,000, with `007`, and
with `5` followed by `extra` exit with status 0 and write ten decimal counts that sum to N, 7 for
`007` and 5 for `5 extra`.  No run writes to stderr.  A native run with N of 1,000 under strace
makes only `getrandom`, `write`, and `exit_group` calls, two of them `getrandom` with flags 0, of
4,096 and 3,904 bytes, each answered with all of its bytes, and a native run with `abc` under
strace makes only `exit_group`.  The driver prints `random histogram axiom check passed for 14
theorems`, the executable's size, and `random histogram: 47 runs passed`.

The second, third, and fourth commands run the module, the executable, and the executable under
QEMU's user-mode emulator with N of 1,000, after the driver has written them.  Each writes ten
lines, the counts of the words whose residue mod 10 is 0, 1, and so on to 9, each in decimal without
a leading zero, which sum to N, and exits with status 0.  One run of the executable wrote `97`, `97`,
`96`, `94`, `88`, `102`, `109`, `99`, `113`, and `105`.

`tests/linux/a64-wasi.sh` writes the executable from the module that `tools/Emit.lean` emits and
elaborates the executable's theorems beside it, which requires the three axioms of each.
[The verified driver](../../tests/verified/run.sh) runs the 74 samples of [the verified
cases](../../Verified/Examples/Cases.lean) in Wasmtime against the specifications, and each case of
`histogram` and `render` requires two blocks to stay allocated after the call, the argument's and
the result's.  [The native driver](../../tests/native/verified.sh) runs the same cases on the
module's translation to C, compiled with CompCert, and `tests/baremetal/verified.sh --module
randomHistogram` runs them on that translation under QEMU without an operating system.  All 74 pass
in each.

## Related examples

[The flat call example](../../Verified/Examples/WasiSys.lean) calls `args` and `randomGet` in a
command, and [its total theorem](../../Verified/Examples/WasiSysTotal.lean) bounds the copies of the
argument bytes.  [The readAll message corollary](../../Verified/Examples/WasiReadAllMessage.lean)
states the output and status of a command over the events of every run, as `exec_main` does, and
[its executable's theorems](../../tests/TestSupport/A64/ImageFilesWasiElf.lean) state it for a
native executable, as `histogram_elf_counts` does.  [The running
maximum](../../Examples/RunningMax/README.md) is a run of the verified-request skill on words, and
[the ranked-choice tabulator](../Rcv/README.md) states call theorems over buffers.

## References

- [Verified Compiler Manual](../../docs/verified-manual.md)
- [Verified WASI Manual](../../docs/wasi.md)
- [`Verified.Call`](../../Verified/Call.lean)
- [WASI Preview 1 declarations](https://github.com/WebAssembly/WASI/blob/fae981bae14809d91f9bc2d63852d461f331d161/preview1/witx/wasi_snapshot_preview1.witx)
- [Linux `fs/exec.c`, v6.12](https://github.com/torvalds/linux/blob/v6.12/fs/exec.c)
- [Linux `fs/exec.c`, v4.13](https://github.com/torvalds/linux/blob/v4.13/fs/exec.c)
- [Linux `drivers/char/random.c`, v6.12](https://github.com/torvalds/linux/blob/v6.12/drivers/char/random.c)
- [getrandom(2)](https://man7.org/linux/man-pages/man2/getrandom.2.html)
- [write(2)](https://man7.org/linux/man-pages/man2/write.2.html)
- [pipe(7)](https://man7.org/linux/man-pages/man7/pipe.7.html)
